# Critique log — AB Ch.6 pp.108–111

Append one section per critic round. Newest at the bottom.

## U1 — round 1 — REVISE

Independent verification: `lake build TCSlib.Complexity.CircuitComplexity` exits 0
(3022 jobs, no errors/warnings). No `sorry` in the module (the only match is the
word "sorry" inside prose at SizeClasses.lean:28). `#print axioms` on
`Language.InSIZE.mono`, `Language.InSIZE.inPPoly`, `ACP.allOnes_inSIZE_one`,
`ACP.allOnes_inSIZE_linear`, `ACP.allOnes_inPPoly`, `ACP.allOnesFamily_language`,
`ACP.mem_allOnes_iff`, `ACP.allOnesCircuit_size`, `ACP.allOnesFamily_onlyUsesGates`,
`ACP.prod_fin_two_eq_one_iff` — all `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`. Line counts confirmed: 148 total, 51 comment, 72 code, 25 blank;
module docstring lines 3–33 = 31 lines. Comment < code and docstring < 40, so the
numeric half of Blocking 7 passes.

### Blocking

- [Blocking] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:92 — `allOnesCircuit_eval`
  has no docstring, violating Blocking 6 ("every declaration has a docstring").
  → add a one-line docstring, e.g. `/-- The circuit computes the product of its inputs. -/`.
- [Blocking] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:109 — `allOnesFamily_circuit`
  has no docstring (same rule). → add one line, e.g.
  `/-- The family's length-`n` circuit is `allOnesCircuit n`. -/`.
- [Blocking] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:122 — the docstring
  "`allOnes` really is `{1ⁿ : n ∈ ℕ}`; in particular `ε = 1⁰` belongs to it" restates the
  module-block decision already recorded at line 21 ("`n = 0` is included: `1⁰ = ε`").
  Blocking 7 forbids restating a design decision in the declaration docstring beneath it.
  → cut the second clause; keep "`allOnes` is exactly `{1ⁿ : n ∈ ℕ}`."
- [Blocking] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:135 — "One unbounded `AND`
  gate suffices" restates the divergence already recorded at line 19 ("ours is one unbounded
  `AND` gate (`size = 1`, depth `1`)"). → state the fact only: "`{1ⁿ : n ∈ ℕ} ∈ SIZE(1)`."

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:37 — the docstring's second
  clause ("AB Definition 6.2 asks only for an upper bound on `|Cₙ|`") argues why the lemma
  holds rather than stating what it is. → keep only "Enlarging the size bound enlarges the class."
- [Advisory] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:18 — AB (PDF p.134, book
  p.108) literally writes `{1ⁿ : n ∈ Z}`, which admits a reading on which `ε ∉ L`; the whole
  `n = 0` story in this file turns on rejecting that reading, but the docstring never quotes
  AB's `ℤ`. → say "AB writes `{1ⁿ : n ∈ ℤ}`; we read it as `n ≥ 0`" where the `n = 0`
  decision is recorded.
- [Advisory] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:73 —
  `finTwoEquiv_symm_eq_one_iff` is a fact about Mathlib's `finTwoEquiv` with nothing to do
  with circuits, yet it lands as `ACP.finTwoEquiv_symm_eq_one_iff`. → move it to the root
  namespace, or to `PPoly.lean` beside `CircuitFamily.Accepts`, which is the only place the
  `Bool`/`Fin 2` boundary is crossed.
- [Advisory] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:120 — `allOnes` is a
  `Language Bool`, but sits in `namespace ACP`, the circuit namespace. `PPoly.lean` puts
  language-level notions in `Language` (`Language.InSIZE`, `Language.InPPoly`) and circuit
  machinery in `ACP`. → `Language.allOnes`, with `mem_allOnes_iff` following it. U2
  (`UnaryLanguages.lean`) is language-level and will inherit the mismatch.
- [Advisory] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:56 — `andGateOp` and
  `andGateOp_mem_AC_GateOps` belong next to `modGateOp` and `AC_GateOps` in
  `TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean`; `AC_GateOps` (ACpGates.lean:30)
  currently inlines the identical anonymous term `⟨Fin n, fun x ↦ ∏ i, x i⟩`, so the gate is
  now written twice in the library. → relocate, and restate `AC_GateOps` via `andGateOp`.
- [Advisory] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:77 — `allOnesNodes` is a
  public `def` that is purely an implementation detail of `allOnesCircuit`; nothing outside
  the file needs it. Its non-irreducibility is not in fact fragile (a plain `def` with a
  matcher unfolds at default transparency, which is why lines 88, 89, 93, 97 and 109 close by
  `rfl`), but it does not belong in the public API. → `private def`.
- [Advisory] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:92 — the lemma is about
  `eval₁`, not `eval`. → rename to `allOnesCircuit_eval₁`.

### Checked and cleared (no finding)

- Faithfulness of the size claim: AB Example 6.3 asserts only "can be decided by a
  linear-sized circuit family". `allOnes_inSIZE_linear : InSIZE (fun n => n + 1)` is exactly
  that, and deriving it from the strictly stronger `InSIZE (fun _ => 1)` via `InSIZE.mono` is
  sound, not a weakening. The one-gate-vs-AND-tree divergence is recorded at lines 18–21, and
  `n + 1` rather than `n` is the right shape given `PPoly.lean`'s `a * (n + 1) ^ k` convention
  (lines 35–36), which exists precisely to repair `|C 0| ≤ 0`.
- `n = 0`: verified in Lean that `allOnesFamily.Accepts []` holds (`andGateOp 0` is the empty
  product `1`) and that `[] ∈ allOnes`. `mem_allOnes_iff` (line 123) states
  `w ∈ allOnes ↔ w = List.replicate w.length true`, which pins `allOnes` to `{1ⁿ}` exactly —
  not something weaker.
- Blocking 3, non-degeneracy: `allOnesFamily.finite` (lines 103–106) is discharged concretely
  per layer (`Finite (Fin n)`, `Finite Unit`), and `allOnesCircuit_size` (line 96) proves
  `Nat.card (Σ _ : Fin 1, Unit) = 1`, a positive value, so the `Nat.card`-returns-0 trap is
  genuinely avoided. Verified independently that `allOnes ≠ Set.univ` and that
  `¬ allOnesFamily.Accepts [false]`, so neither the language nor the family is vacuous.
- `prod_fin_two_eq_one_iff` (line 63) is not speculative generalization: it is consumed at
  line 131 in this file, and U2 needs it. No equivalent exists in TCSlib, and no Mathlib
  one-liner covers it directly. Only its namespace is questionable (see the `finTwoEquiv`
  item); the generality over `ι` is the natural statement.
- Both `@[simp]` lemmas (lines 91, 108) are canonical and normalizing: each replaces a
  local `def` with the general expression it abbreviates.
- Alphabet convention is consistent: `allOnes` is over `Bool`, `andGateOp`/`allOnesCircuit`
  are over `Fin 2`, and `finTwoEquiv` appears only at the boundary (`PPoly.lean:63` and the
  boundary lemma at line 73).
- Scope: everything in the file is within U1 as `ch6/PLAN.md` defines it, including the
  Theorem 6.6 deferral docstring (lines 26–32), which U5 explicitly asks for. No `sorry` stub
  was written for it, as U5 requires.
- Style: absence of a copyright header matches the immediate neighbours
  (`Basic.lean`, `Formulas.lean`, `DecisionTree.lean`, `PPoly.lean` all lack one).

## U1 — round 2 — PASS

Independent verification: `lake build TCSlib.Complexity.CircuitComplexity` exits 0
(3022 jobs, no errors or warnings). `#print axioms` run by me on all fourteen
public declarations — `Language.InSIZE.mono`, `.inPPoly`, `finTwoEquiv_symm_eq_one_iff`,
`Language.mem_allOnes_iff`, `ACP.andGateOp_mem_AC_GateOps`, `ACP.prod_fin_two_eq_one_iff`,
`ACP.allOnesCircuit_eval₁`, `ACP.allOnesCircuit_size`, `ACP.allOnesFamily_circuit`,
`ACP.allOnesFamily_onlyUsesGates`, `ACP.allOnesFamily_language`,
`Language.allOnes_inSIZE_one`, `_inSIZE_linear`, `_inPPoly` — every one is
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`. Counted 141 lines /
46 comment / 72 code / 23 blank; all 19 declarations carry a docstring
(checked mechanically, not by eye). No dangling references to the renamed or
moved declarations anywhere in `TCSlib/`.

### Round 1 Blocking findings — all four resolved, dropped

- :92 `allOnesCircuit_eval₁` now has a docstring (line 90), and took the Advisory rename.
- :110 `allOnesFamily_circuit` now has a docstring (line 108).
- :49 `mem_allOnes_iff` docstring no longer restates the `n = 0` decision.
- :130 `allOnes_inSIZE_one` docstring no longer restates the AND-gate divergence.

### Round 1 Advisory findings — six resolved, dropped

- :76 `allOnesNodes` is now `private`; `#check_failure ACP.allOnesNodes` confirms it is
  genuinely inaccessible, and the `rfl` proofs at lines 87, 88, 93, 97 and 110 still
  close, as predicted — privacy does not affect transparency.
- :43 `finTwoEquiv_symm_eq_one_iff` moved to the root namespace (one of the two fixes
  round 1 offered).
- :18 the docstring now quotes AB's `{1ⁿ : n ∈ ℤ}` and states the reading.
- :31 `InSIZE.mono` docstring restated as a fact.
- :47 `allOnes` moved to `Language` — see the ruling below.
- Relocating `andGateOp` into `ACpGates.lean` is deferred by the coordinator; not re-raised.

### Ruling on the namespace split — the formalizer did not overreach

Moving `allOnes_inSIZE_one`, `_inSIZE_linear` and `_inPPoly` into `Language` alongside
`Language.allOnes` and `Language.mem_allOnes_iff` is correct and was implied by the
round 1 finding, not beyond it. All three state `Language.allOnes.InSIZE …` or
`.InPPoly`; both head constants of the subject (`Language.allOnes`, `Language.InSIZE`)
live in `Language`, and the placement is what makes the `Language.allOnes_inSIZE_one.mono`
dot-chain at line 137 read correctly. Leaving `ACP.allOnes_inPPoly` beside
`Language.allOnes` would indeed have reinstated the split the finding removed.

`ACP.allOnesFamily_language` (line 121) is on the correct side. Mathlib names a theorem
after the head of its left-hand side; here that is `ACP.allOnesFamily.language`, a
projection of `ACP.CircuitFamily`, with `Language.allOnes` appearing only on the right.
It is also the fourth of the four `allOnesFamily_*` facts and belongs with them.

The boundary that results is statable in one line — `ACP` holds every declaration whose
statement mentions a circuit, `Language` holds every one that does not — and the file
honours it exactly.

### Ruling on the deleted `/-! ## ... -/` section markers — acceptable

The file is navigable without them, not merely shorter. `PPoly.lean` (118 lines) uses
none, the `## Main results` list at lines 6–11 orients a reader, and the single
`namespace ACP` / `end ACP` block at 54–128 is the one structural division the file
needs at 141 lines. The root namespace is now opened, closed and reopened around it
(31–52, 54–128, 130–141), which is slightly unusual but follows from the corrected
namespace split rather than from the marker deletion.

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:6 — the `## Main results`
  list names `ACP.allOnesFamily` and the three `Language.allOnes_*` theorems but never
  names `Language.allOnes` itself, the definition the whole module is about; a reader
  scanning the header cannot learn what it is called. (Latent in round 1 too; I did not
  raise it then, and it does not block.) → add a line for `Language.allOnes`.

### Report inaccuracies (no defect, recorded because the report was not to be trusted)

- "zero `sorry` (the word no longer appears at all)" is false: `sorry` appears at line 25,
  inside the Theorem 6.6 deferral prose. That sentence is correct and is what `PLAN.md` U5
  asks for — there is no `sorry` term and no stub — but the claim about it is wrong.
- The module docstring spans lines 3–29, which is 27 lines, not the 30 claimed. Under the
  ~40 limit either way.
- Comment count 46 matches my counter this round. In round 1 the two counters disagreed
  (48 claimed vs 51 measured), so the round-1 "down from 48 to 46" delta is not meaningful;
  the measured delta is 51 → 46.

Verdict: **PASS** — zero Blocking. U1 flipped to `DONE` in `ch6/PLAN.md`.

## U3 — round 1 — REVISE

Independent verification (nothing below is taken from the formalizer's report).
`lake build TCSlib.Complexity.CircuitComplexity.CircuitSat` exits 0 (3015 jobs);
`lake build TCSlib.Complexity.CircuitComplexity` — the subtree with `CircuitSat`
now registered in the aggregator — exits 0 (3028 jobs), no errors, no warnings.
`grep -n sorry CircuitSat.lean` returns nothing (exit 1): the word does not occur,
in code or in prose. `#print axioms` run by me on all fourteen non-`def`
declarations — `Circuit.eval_lit`, `.eval_node_true_iff`, `.eval_node_false_iff`,
`mem_cktSat_iff`, `evalLiteral_toLiteral_iff`, `evalLiteral_toLiteralNeg_iff`,
`gateClauses_satisfied`, `tseitin_satisfied`, `eval_node_iff_of_gateClauses`,
`eval_iff_of_tseitin_satisfied`, `Circuit.satisfiable_iff_isSatisfiable`,
`mem_cktSat_iff_is3Satisfiable`, `Circuit.tseitin_length_le`,
`Circuit.toCNF_length_le` — no `sorryAx`. Twelve are
`[propext, Classical.choice, Quot.sound]`; the two literal lemmas are `[propext]`
alone. Counted 359 total / 243 code / 70 comment / 46 blank; module docstring
lines 9–45 = 37 lines. All four self-reported numbers are correct this round —
unlike U1, the report checks out on every count I could measure.
All 23 declarations carry a docstring (checked mechanically, not by eye).

### Blocking

- [Blocking] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:31 — "There being no
  machine model here, the reduction's running time is likewise replaced by the explicit
  bound `toCNF_length_le`." `toCNF_length_le` bounds the *clause count* of the
  intermediate `C.toCNF`, and nothing else. It is not a substitute for a running-time
  or output-size claim, for three independent reasons: (i) clause width is unbounded —
  by the file's own design (lines 42–43) a fan-in-`w` `AND` emits one clause of width
  `w + 1` — so clause count does not bound formula size; (ii) the object the headline
  theorem is about is `to3SAT C.2.toCNF`, not `C.toCNF`, and `SATTo3SAT.lean` proves no
  length bound on `to3SAT` at all (I grepped: the only `to3SAT` + `length` occurrences,
  lines 259/267/291, are membership characterisations); (iii) `CktVar n` is an infinite
  variable type, so "the reduction's output" is not a finite object the file ever
  measures. Recording a divergence by pointing at a lemma that does not discharge it is
  worse than not recording it. → state the fact: the `≤p` of AB Lemma 6.11 is *not*
  formalized — only equisatisfiability is — and `toCNF_length_le` is a clause-count
  bound on the intermediate CNF, with nothing proved about `to3SAT C.toCNF`. Qualify the
  `## Main results` line 24 ("AB Lemma 6.11") the same way.
- [Blocking] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:37 — "Satisfiability is
  insensitive to the choice (`ACP.FeedForward.toCircuit` preserves `eval`)" cites a lemma
  that does not support it, and contradicts line 36. `ACP.FeedForward.toCircuit`
  (FeedForwardCircuit.lean:216) has signature
  `(F : FeedForward Bool (Fin n) out) (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
  (gfin : ∀ d v, Fintype (F.gates d v).op.ι) (o : out)`. Two gaps: it is over
  `FeedForward Bool`, whereas `PPoly.lean`'s `ACP.CircuitFamily.circuit` is
  `FeedForward (Fin 2) (Fin n) Unit` (PPoly.lean:52), so it does not apply to the model
  line 34 says it bridges without `finTwoEquiv` transport; and it demands an explicit
  `isAnd` tag per gate, which is exactly the datum line 36 correctly says `AC_GateOps`
  membership cannot yield ("membership in `AC_GateOps` is a `Prop`, so no clause map can
  case on it"). The docstring therefore asserts a model equivalence the library does not
  have. → drop the parenthetical, or restate it as what is true: `toCircuit_eval`
  (FeedForwardCircuit.lean:223) preserves `eval` for a `FeedForward Bool` circuit whose
  gates come with an `isAnd` tag and finite fan-in, which `ACP.CircuitFamily` does not
  supply; no bridge from `PPoly.lean`'s model to `BoolCircuit.Circuit` exists yet.

### Ruling on `CktSat : Set ((n : ℕ) × Circuit n)` — legitimate scoping, not a different object

This is the call that mattered most, and the formalizer got it right. AB Definition 6.9
(PDF p.136, book p.110) reads "the language CKT-SAT consists of all (strings
representing) circuits that produce a single bit of output and that have a satisfying
assignment" — AB's own parenthetical marks the encoding as bookkeeping, and the next
sentence restates the content encoding-free: "a string representing an n-input circuit C
is in CKT-SAT iff there exists u ∈ {0,1}ⁿ such that C(u) = 1". `Circuit.Satisfiable`
(line 81) is that sentence verbatim. The encoding is load-bearing only for Lemma 6.10's
"polynomial-time transformation from M, x to a circuit C", which `ch6/PLAN.md` has
already marked SKIP, and for the polynomial-time half of Lemma 6.11 — which the first
Blocking item is about, and which no encoding in this file would repair. `PLAN.md` U3
specifies "`CktSat`: circuits with a satisfying assignment" in as many words, so this is
inside scope, not a unilateral redefinition. The divergence is recorded at lines 29–31.
AB's "produce a single bit of output" is discharged structurally: `BoolCircuit.Circuit`
is single-output by construction. Cleared.

### Checked and cleared (no finding)

- **Non-degeneracy (Blocking 3), verified by compiling, not by reading.** The two
  `example`s at lines 97 and 100 typecheck. Beyond them I compiled: `⟨1, node true [x₀]⟩
  ∈ CktSat` and `⟨1, node true [x₀, ¬x₀]⟩ ∉ CktSat`, so `CktSat` is non-trivial at
  positive arity too, not only on the empty gate list; `CktSat ≠ Set.univ`. The empty-gate
  cases are *not* vacuous: I proved `gateClauses true [] = [[pos (gate (node true []))]]`
  and `gateClauses false [] = [[neg (gate (node false []))]]` — each emits a unit clause
  pinning the gate variable to the correct value of the empty conjunction/disjunction,
  so an unbounded-fan-in clause map does not go silently empty at width 0. End-to-end:
  `¬ is3Satisfiable (to3SAT (toCNF (node true [x₀, ¬x₀])))` and
  `is3Satisfiable (to3SAT (toCNF (lit x₀)))` both compile, so the composite reduction is
  non-vacuous in both directions through `to3SAT`. At `n = 0`, `toCNF (node true [])` has
  length 2 and `size = 1`, so `toCNF_length_le` (`2 ≤ 3`) is a real inequality, not `0 ≤ 0`.
- **The three `Circuit.eval_*` lemmas (lines 58, 63, 71) are the correct call.** They are
  general facts about `Basic.lean`'s `Circuit.eval`, but the file-ownership rule in
  `REVIEW_CRITERIA.md` forbids this agent from editing `Basic.lean`. I grepped `TCSlib/`:
  no `eval_node_true_iff` / `eval_node_false_iff` / `Circuit.eval_lit` exists anywhere
  else, so Blocking 4 (no redefinition) is satisfied — nothing is duplicated. Flagged for
  relocation in the cross-cutting pass; a row is added to `ch6/PLAN.md`.
- **Choice usage is inherent, not sloppy.** The `classical` at line 300 exists because
  `SATTo3SAT.Assignment V := V → Prop` is `Prop`-valued, so extracting `u : Fin n → Bool`
  from `α` at line 310 needs `Classical.propDecidable`. Reusing `SATTo3SAT`'s vocabulary
  is what `PLAN.md` U3 mandates ("Reuse, do not re-derive"), and every Mathlib-dependent
  result in U1 already carries `Classical.choice`. No finding. Note in passing that
  `evalLiteral_toLiteral_iff` and `_toLiteralNeg_iff` come out `[propext]`-only, so the
  choice is confined to the soundness direction as claimed.
- **Reuse (Blocking 4).** `Literal`, `Clause`, `CNFFormula`, `Assignment`, `evalLiteral`,
  `clauseSatisfied`, `formulaSatisfied`, `isSatisfiable`, `is3Satisfiable`, `to3SAT`,
  `SAT_to_3SAT_equivalence` are all taken from `SATTo3SAT.lean`; nothing is re-derived.
  `Formulas.lean:22` defines a *different* `BoolCircuit.Literal (n : ℕ)`, but it is not
  imported by this file and I confirmed downstream `open BoolCircuit SATTo3SAT` still
  elaborates `Literal.pos` unambiguously. Not a hazard.
- **Tseitin sharing is sound.** `CktVar.gate : Circuit n → CktVar n` gives structurally
  equal subcircuits the same variable; `tseitinAssignment` (line 143) sends `.gate D` to
  `D.eval u`, which is a function of `D`, so sharing cannot conflict in either direction.
- **The `NOT`-gate remark (lines 39–40) is accurate.** For a leaf with `sign = true` the
  pair at lines 132–133 is `z ↔ xᵢ`; only at `sign = false` does it become AB's
  `zᵢ ↔ ¬z_j`. "Occurs exactly at a negative leaf" is the right statement.
- **Comment budget (Blocking 7), numeric half.** 70 comment vs 243 code, and a 37-line
  module docstring — both inside the limits, though 37 is close enough to ~40 that the
  Blocking fixes above should shorten rather than extend the block.
- **Every declaration has a docstring (Blocking 6).** All 23, checked mechanically.
- **Copyright header (Advisory 11).** `CircuitSat.lean` is the only file in
  `CircuitComplexity/` with one, which looks like drift — but `Copyright (c)` headers are
  the norm across the rest of `TCSlib/` (`NPReductions/*`, `RazborovSmolensky/*`,
  `BLR/*`, `GraphTheory/*`), including the very file being reused, `SATTo3SAT.lean`, and
  "Yichuan Wang" is an existing author in this repo. The neighbours are the outliers.
  No finding.

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:329 —
  `Circuit.tseitin_length_le` states `C.tseitin.length + 1 ≤ 3 * C.size`, i.e. a strict
  `<`. Mathlib names that `_lt`; `_le` says something the theorem does not say
  (Blocking 5's "named after what they say" — I do not block because the declaration
  docstring, "number fewer than `3 * C.size`", is accurate). → rename to
  `Circuit.tseitin_length_lt`, or restate as `C.tseitin.length < 3 * C.size`.
- [Advisory] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:107 — `CktVar n` is
  indexed by *every* `Circuit n`, not by the nodes of the `C` under reduction, so the
  formula's variable type is infinite. Harmless for satisfiability, and the reason no
  output-size claim is statable. → record it in the divergence block alongside the first
  Blocking fix; it is the same fact seen from the variable side.
- [Advisory] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:35 — "A `FeedForward`
  gate is an opaque `(ι → α) → α` whose membership in `AC_GateOps` is a `Prop`, so no
  clause map can case on it" argues why the design choice was made rather than stating
  it. `PPoly.lean`'s divergence block is terser per divergence. → compress to the fact
  ("`AC_GateOps` membership is a `Prop`, so `FeedForward` gates cannot be cased on").
  The clause is correct and is what justifies the second Blocking fix, so keep one line
  of it; do not delete outright.
- [Advisory] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:322 — the right-hand
  side of `mem_cktSat_iff_is3Satisfiable` is `is3Satisfiable (to3SAT C.2.toCNF)`, a
  predicate on one formula, not membership in a `3SAT` object. So neither side of the
  claimed `≤p` is a language and the relation is equisatisfiability, not a reduction
  between languages. → once a `ThreeSat` set exists (U4 or the cross-track pass), restate
  as a membership-to-membership iff; until then, do not write `≤p` unqualified.
- [Advisory] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:58 — `Circuit.eval_lit`,
  `Circuit.eval_node_true_iff`, `Circuit.eval_node_false_iff` (58, 63, 71) belong in
  `Basic.lean` beside `Circuit.eval`. Correctly parked here under file ownership; queued
  as a deferred follow-up in `ch6/PLAN.md` rather than re-raised each round.

Verdict: **REVISE** — two Blocking. Both are docstring-accuracy defects, not proof
obligations: no Lean code needs to change, and I am not asking for a polynomial bound
to be proved. U3 stays `WIP` in `ch6/PLAN.md`.

## U3 — round 2 — PASS

Independent verification. `lake build TCSlib.Complexity.CircuitComplexity` exits 0,
**3029 jobs**, no errors or warnings — the subtree now also carries U2's
`UnaryLanguages.lean` (aggregator line 6) and is green with it. `grep -c sorry` = 0.
`#print axioms` run by me on all **fourteen** non-`def` declarations, not the eight
claimed, including the renamed `Circuit.tseitin_length_lt`: no `sorryAx`; twelve are
`[propext, Classical.choice, Quot.sound]`, the two literal lemmas `[propext]` alone.
All 23 declarations still carry a docstring (checked mechanically). No dangling
reference to the old name `tseitin_length_le` anywhere in `TCSlib/`.

**The number that mattered: the module docstring is lines 9–46 = 38 lines.** Confirmed
by reading line 9 (`/-!`) and line 46 (`-/`) directly. Under the ~40 limit with 2 lines
of slack, as claimed. Counted 360 total / 243 code / 71 comment / **46** blank — the
report said 47 blank, which is off by one (243 + 71 + 46 = 360 checks out; the other
three numbers are exact). Comment 71 < code 243.

### Round 1 Blocking findings — both genuinely resolved, not reworded. Dropped.

- **:31 → now :29–35.** The block opens "Only equisatisfiability is formalized, not
  `≤p`: TCSlib has no machine model, and this file proves no bound on the reduction's
  cost", then gives all three reasons I raised, each checkable: `toCNF_length_le`
  "counts the clauses of the intermediate `C.toCNF` and no more", clause width is
  unbounded, "`SATTo3SAT` bounds nothing about `to3SAT`", and `CktVar n` is infinite.
  This is the substance of the finding, not a softening of it. `## Main results` line 24
  now reads "AB Lemma 6.11, **equisatisfiability only**". The string `≤p` now occurs
  exactly once in the file (line 29), inside the sentence that disclaims it — I grepped.
- **:37 → now :37–41.** The `ACP.FeedForward.toCircuit` citation is gone entirely, and
  the paragraph now asserts the opposite of what it used to: "No equivalence of the two
  models is claimed, and none is available here." The reason kept is the sound one — a
  `FeedForward` gate is an opaque `(ι → α) → α` whose `AC_GateOps` membership is a
  `Prop`, so no clause map can case on it. The `Bool`/`Fin 2` mismatch and the missing
  `isAnd` tag are recorded as a deferred follow-up in `ch6/PLAN.md`, which is where a
  cross-model gap belongs.

### Round 1 Advisory findings — four applied, verified

- **:329 rename applied and the statement really is strict.** `Circuit.tseitin_length_lt`
  now reads `C.tseitin.length < 3 * C.size`, not `length + 1 ≤ …`; name and statement
  agree, and the docstring "number fewer than `3 * C.size`" is now literally the theorem.
- **`toCNF_length_le` correctly keeps `≤`, and I checked rather than took it on trust.**
  It cannot be strengthened: `toCNF.length = tseitin.length + 1`, and I compiled
  `(toCNF (lit x₀)).length = 3 * (size (lit x₀))` — equality is attained at a leaf
  (3 = 3 * 1), so `<` would be false. The formalizer's reasoning here is right.
- **:107 `CktVar` infiniteness** is recorded, at line 32, inside the same sentence that
  explains why no cost bound is statable — which is the right place for it, since it is
  that fact seen from the variable side.
- **:35 model-choice paragraph** compressed from 7 lines to 5 (now 37–41), keeping the
  one clause that carries the argument, as asked.
- **:322 `≤p` removed** from `mem_cktSat_iff_is3Satisfiable`'s docstring (now line 321),
  which reads "**Arora–Barak Lemma 6.11**: a circuit is satisfiable exactly when the
  3-CNF formula built from its gate clauses is" — names the AB result, as Blocking 6
  requires, without asserting the polynomial-time content.

### Ruling: `Circuit.toCNF_length_le` **stays in `## Main results`**

The formalizer raised this itself rather than waiting to be caught, which is the right
instinct, and the answer is that it stays. Three reasons.

It is a real result of this unit, not scaffolding: it is proved by a genuine structural
induction (lines 330–352) and it is the file's only quantitative content. Advisory 7
positively favours exactly this shape — an exact, coercion-free, ℕ-native pointwise
bound rather than an asymptotic one — so deleting it to avoid an implication would trade
a true theorem for a presentational worry, which is the wrong direction.

The worry it might mislead is answered five lines below it, in the same docstring block:
line 30 says `toCNF_length_le` "counts the clauses of the intermediate `C.toCNF` and no
more". A reader who reaches line 25 reaches line 30. The two are not in tension; the
header names the result and the Divergences block bounds what it means, which is
precisely the division of labour `PPoly.lean` uses.

And demoting it out of the headline list would make the file's one measured fact
undiscoverable from the header, for no gain — `## Main results` lists what is proved, not
what discharges AB's wording. Nothing else in the list discharges AB's wording either;
line 24 now says so explicitly.

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:25 — `## Main results`
  says `toCNF_length_le` bounds "the output", but line 30 of the same block is careful to
  call `C.toCNF` the *intermediate* formula, the output being `to3SAT C.toCNF`. The two
  lines disagree on one word. This is not the round 1 Blocking item returning — that was
  line 24, and it was fixed — and it does not block: line 25 says "clauses", which is
  accurate, and line 30 governs. → "the intermediate `C.toCNF` has at most `3 * C.size`
  clauses". One word, no net lines, so it fits inside the budget constraint.
- [Advisory] TCSlib/Complexity/CircuitComplexity.lean:30 — **orchestrator-owned, reported
  not edited.** The aggregator still blurbs `CircuitSat` as "the Tseitin reduction
  `CKT-SAT ≤p 3SAT` (AB Lemma 6.11)". After this round that is the one place in the
  subtree still asserting `≤p` unqualified — the module it describes now explicitly
  disclaims it. → match `CircuitSat.lean:24`: "…the Tseitin reduction to 3SAT (AB Lemma
  6.11, equisatisfiability only)".

### On the comment budget

The constraint is fair and I am respecting it: neither advisory above asks for a net
addition, and I am asking for no new divergence text. With 2 lines of slack at 38, the
block is at its working limit — any future divergence to record should displace
something, and the first candidate is the fan-in paragraph's last sentence ("Equal
subcircuits share a variable — Tseitin sharing", line 45), which restates what
`CktVar.gate : Circuit n → CktVar n` already makes evident at the definition.

### Still cleared from round 1, re-verified after the edit

Non-degeneracy: I recompiled the full set — the two `example`s, `CktSat` non-trivial at
arity 1 in both directions, and end-to-end `¬ is3Satisfiable (to3SAT (toCNF (node true
[x₀, ¬x₀])))` with its satisfiable counterpart. All still close. The edit was confined to
prose plus one rename; no proof changed, and the axiom profile is identical to round 1.

Verdict: **PASS** — zero Blocking. U3 flipped to `DONE` in `ch6/PLAN.md`.

## U2 — round 1 — REVISE

Independent verification (nothing below is taken from the formalizer's report).
`lake build TCSlib.Complexity.CircuitComplexity` exits 0, **3029 jobs**, no errors
or warnings — so the whole registered subtree is green, not just this module. The
report's "3020 jobs" is wrong; U1 round 2 measured 3022 and `CircuitSat.lean` has
been registered since, which accounts for the rise.

`#print axioms` run by me on all **17** public declarations — `Language.le_allOnes_iff`,
`Language.exists_le_allOnes`, `ACP.notGateOp`, `ACP.notGateOp_mem_AC_GateOps`,
`ACP.constZeroCircuit`, `ACP.constZeroCircuit_eval₁`, `_size`, `_finite`,
`_onlyUsesGates`, `ACP.unaryFamily`, `ACP.unaryFamily_circuit_of_mem`,
`_circuit_of_not_mem`, `_onlyUsesGates`, `_size_le`, `_language`,
`Language.inSIZE_two_of_le_allOnes`, `Language.inPPoly_of_le_allOnes` — every one is
`[propext, Classical.choice, Quot.sound]` (`ACP.notGateOp` is `[propext]` alone).
No `sorryAx`. `#check_failure ACP.constZeroNodes` confirms the private def is
genuinely inaccessible.

`grep -n sorry` on the file returns **zero** matches, prose included. That claim is
true this round.

Line counts: **176 total / 104 code / 43 comment / 29 blank**. The report's
"50 comment / 22 blank" is reachable only by counting the 7 blank lines *inside*
the module docstring block as comment; 50 + 22 = 43 + 29 = 72 either way, and
comment < code under both conventions, so Blocking 7's numeric half passes. Module
docstring spans lines 3–31 = **29 lines**, under ~40; the report's 29 is right.
All **18** declarations (17 public + `constZeroNodes`) carry a docstring, checked
mechanically, not by eye.

AB page read: PDF 136 = book 110. Claim 6.8 is "Let L ⊆ {0,1}* be a unary language
(i.e., L ⊆ {1n : n ∈ N}). Then L ∈ P/poly", proved by "a circuit family of linear
size. If 1n ∈ L, then the circuit for inputs of size n is the circuit from
Example 6.3, and otherwise it is the circuit that always outputs 0." The file
formalizes exactly that. Note AB writes **ℕ** here, not the `ℤ` of p.108 — which
retrospectively settles U1 round 1's advisory about the `ℤ` reading in AB's favour.

### Blocking

- [Blocking] TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean:67 — the
  `constZeroNodes` docstring, "The three layers of `constZeroCircuit n`: the `n`
  inputs, the empty `AND`, then its negation", restates the construction already
  recorded in the Design block at lines 17–18 ("the empty `AND` is the empty product
  `1`, and `NOT` of that is `0`"). Blocking 7 forbids restating a design decision in
  the declaration docstring beneath it; this is the same defect U1 round 1 blocked on
  at SizeClasses.lean:135. The gate roles belong to `constZeroCircuit` (line 74), not
  to a `Fin 3 → Type`. → say what the def is and stop: "The three layers of
  `constZeroCircuit n`: the `n` inputs, then two singleton layers." U1's surviving
  counterpart (`allOnesNodes`, SizeClasses.lean:76) names no gates, which is why it
  passed.
- [Blocking] TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean:11 — the
  `## Main results` bullet "`ACP.unaryFamily` — Claim 6.8's family: `allOnesCircuit n`
  when `1ⁿ ∈ L`, `constZeroCircuit n` otherwise" is a paraphrase of the declaration
  docstring 100 lines later at :111–112 ("Claim 6.8's family for `L`: the all-ones
  circuit at the lengths `n` with `1ⁿ ∈ L`, and the constant-`0` circuit at the
  others"). Two sentences, same content — Blocking 7's "reject on duplicated prose".
  U1's list entries are labels ("`ACP.allOnesFamily` — the circuit family deciding
  it."), which is why they drew no finding. → shorten the bullet to
  "`ACP.unaryFamily` — Claim 6.8's circuit family for a unary `L`." The bullet at
  :10 overlaps :73 the same way but less severely; trim it to label length in the
  same pass.

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean:22 — the
  docstring says `unaryFamily` "chooses between the two branches by `Classical.dec`".
  It does not: `#print` with `pp.all` shows the elaborated term carries
  `Classical.propDecidable`, and the string `Classical.dec` occurs nowhere in the
  file. The two are definitionally the same instance, so this is imprecision rather
  than falsehood, but a reader grepping for what the docstring names finds nothing.
  → write "by `open scoped Classical`", or name `Classical.propDecidable`.
- [Advisory] TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean:17 — "`AC_GateOps`
  has no constant gate, so `constZeroCircuit` builds one out of the two it has" is
  false about the gate set: `AC_GateOps` (ACpGates.lean:27–30) is
  `{GateOp.id, NOT} ∪ ⋃ n {AND_n}` — three gate kinds, not two. The `no constant gate`
  half is correct and is the point worth recording. → "out of the two it uses".
- [Advisory] TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean:88 — the `show`
  in `constZeroCircuit_eval₁` displays `1 - (∏ _i : Fin 0, (1 : Fin 2))`, and the
  `(1 : Fin 2)` is arbitrary decoration: I verified that substituting `(0 : Fin 2)` or
  `(37 : Fin 2)` elaborates and closes identically, and that `show (1 : Fin 2) - 1 = 0`
  followed by `rfl` also closes the goal. So the term a reader is shown is not what
  the layer-1 gate computes — that is the product over the empty wiring
  `fun i : Fin 0 => i.elim0 : Fin 0 → Fin n` — it is merely *one* term the empty
  product is defeq to. → make the `show` name the actual wiring, or add one trailing
  comment: "the layer-1 `AND` is empty, so its value is `1` whatever the inputs are".
- [Advisory] TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean:6 — the
  `## Main results` list omits `Language.inSIZE_two_of_le_allOnes`, which is named
  only inside the Design paragraph at :29. Same shape as U1 round 2's advisory about
  `Language.allOnes`. → add a line for it.

### Rulings the coordinator asked for

**1. `≤` for `⊆` — forced, adequate, and recorded.** I re-verified the premise
independently: `#check_failure (inferInstance : HasSubset (Language Bool))` fails to
synthesize, so `⊆` genuinely does not elaborate. The deviation is recorded at :25–26.
It is also *harmless*, which matters more than that it is forced: I checked that
`(L ≤ M) = (∀ ⦃w⦄, w ∈ L → w ∈ M)` holds by `rfl`, so `≤` on `Language Bool` **is**
set inclusion, reached through the `CompleteAtomicBooleanAlgebra` instance rather than
`HasSubset`. And `Language.le_allOnes_iff` (:34) does genuinely discharge the
faithfulness burden: its right-hand side, `∀ w ∈ L, ∃ n, w = List.replicate n true`,
is AB's `L ⊆ {1ⁿ : n ∈ ℕ}` written out with no reference to any order instance, so a
reader need not trust Mathlib's lattice structure to see that the hypothesis of
`inPPoly_of_le_allOnes` is AB's hypothesis. No finding.

**2. `constZeroCircuit_eval₁` — fragile, but no more so than the U1 proof that
passed.** It would not survive a change to `andGateOp`: the `show` requires
`andGateOp.func` to be syntactically `fun x => ∏ i, x i`, so that at `ι := Fin 0` it
whnf-reduces through `Finset.prod ∅`. Rewrite `andGateOp` as a fold, or via a
`decide`, and the `show` stops elaborating. But the same is true of U1's
`allOnesCircuit_eval₁ ... := rfl` (SizeClasses.lean:93), which passed, and
`FeedForwardCircuit.lean` exposes no `eval₁`-unfolding lemma to go through —
`evalNode` (line 48) is a raw `Nat.recAux`, so there is no "existing lemma" to state
it via. Stating it by defeq is the only idiom the library offers today. Advisory only,
on the misleading displayed term (above), not on the technique.

**3. `Language.exists_le_allOnes` is in U2's scope. U2 owns it.** Blocking 3 requires
a non-vacuity check, and the hypothesis `L ≤ Language.allOnes` is the one thing in
this file that could be vacuous — `inPPoly_of_le_allOnes` would be worthless if the
only unary language were `∅`. `exists_le_allOnes` answers exactly that, for every
`S : Set ℕ`, decidable or not, which is the sharpest form the answer takes. It is not
U4's: U4 needs `n`'s binary expansion encoding `⟨M, x⟩` and the undecidability of the
resulting set, none of which this lemma mentions or needs. U4 should *consume* it, and
when it needs to name the language rather than assert it exists, introduce
`Language.unary` there — not retrofit it here on speculation (Advisory 9). No finding.
For my own part I checked the non-vacuity end to end rather than reading the lemma:
with `Leven := {w ∈ allOnes | Even w.length}` I verified `Leven.InPPoly`,
`(unaryFamily Leven).Accepts [true,true]`, `¬(unaryFamily Leven).Accepts [true]` and
`(unaryFamily Leven).language ≠ Set.univ`, and separately that the two degenerate
ends, `(fun _ => False)` and `Language.allOnes` itself, both go through. The size
trap is avoided too: `constZeroCircuit_size = 2 > 0`, so `Nat.card` is not silently
returning `0`.

**4. Non-uniformity is recorded as a design point, and the `if` lemmas are
instance-agnostic.** :21–23 records it as the *reason* Claim 6.8 holds ("The
per-length choice is what makes Claim 6.8 true, and is how AB then puts an undecidable
language in `P/poly`"), which is the right framing — `noncomputable` here is content,
not a defect, and AB's own proof is non-constructive in exactly this way. On the
instance question: `unaryFamily`'s body fixes `Classical.propDecidable` in the term
once and for all, and `if_pos`/`if_neg` are stated for an arbitrary `[Decidable c]`,
so `unaryFamily_circuit_of_mem`/`_of_not_mem` (:121, :126) rewrite against whatever
instance is baked in — no diamond is possible, and a caller with its own
`DecidablePred (· ∈ L)` cannot create one, because those two lemmas fully mediate
access to the `if`. The claim is correct. The absence of an unconditional
`unaryFamily_circuit` is right, not an omission: there is no single right-hand side
to state. No finding.

**5. Size `2` vs AB's "linear size" — recorded, nothing overclaims.** :28–30 states
the divergence and the derivation ("`a = 2`, `k = 0`"). This is U1's shape — prove
strictly stronger, derive AB — and it is if anything cleaner here, because AB's
numbered claim is `L ∈ P/poly`, not a size bound; "linear size" appears only in AB's
*proof*, so `inPPoly_of_le_allOnes` (:174) is AB's statement verbatim and no weaker
intermediate is owed. `inSIZE_two_of_le_allOnes`'s docstring, "A unary language is
decided by circuits of size `2`", is exact. No finding.

**6. `notGateOp`'s docstring does not misdescribe.** "The `NOT` gate, in the shape
used by `AC_GateOps`" is accurate — I confirmed `ACP.notGateOp = ⟨Fin 1, fun x => 1 - x 0⟩`
by `rfl`, and that term is what `AC_GateOps` inlines at ACpGates.lean:29. The
duplication itself is the recorded deferred follow-up and is not re-raised. I have
extended that row in `ch6/PLAN.md` to cover `notGateOp` as well, since the row named
only `andGateOp` and the cross-track pass needs both.

**Namespace boundary (the U1 rule: `ACP` holds every declaration whose statement
mentions a circuit, `Language` holds every one that does not) — honoured exactly.**
`Language.le_allOnes_iff` and `Language.exists_le_allOnes` mention no circuit;
`inSIZE_two_of_le_allOnes` and `inPPoly_of_le_allOnes` are about `Language.InSIZE` /
`InPPoly`, whose statements mention circuits only inside the *definition*, which is
where U1 put `Language.allOnes_inSIZE_one`. Everything in `namespace ACP` (:56–165)
names a `FeedForward` or a `CircuitFamily`, including `unaryFamily`, which takes a
`Language Bool` but *produces* a circuit family — head of the subject, per Mathlib.
No finding.

### Checked and cleared (no finding)

- Blocking 4, reuse: `andGateOp`, `allOnesCircuit`, `allOnesFamily`,
  `allOnesFamily_language`, `allOnesFamily_onlyUsesGates`, `Language.allOnes`,
  `Language.mem_allOnes_iff` are all taken from U1; nothing is re-derived.
  `notGateOp` is the one new gate and it is the only NOT term outside
  `ACpGates.lean` (`grep` over `TCSlib/` finds `1 - x 0` at ACpGates.lean:29 and
  :587 and nowhere else).
- Blocking 5, naming: `le_allOnes_iff`, `exists_le_allOnes`, `constZeroCircuit_eval₁`,
  `_size`, `_finite`, `_onlyUsesGates`, `unaryFamily_circuit_of_mem`,
  `_circuit_of_not_mem`, `_size_le`, `_language`, `inSIZE_two_of_le_allOnes`,
  `inPPoly_of_le_allOnes` all say what they state. `_eval₁` takes U1's corrected
  suffix rather than repeating U1 round 1's `_eval` mistake.
- The single `@[simp]` (:85) is canonical and normalizing — it sends
  `(constZeroCircuit n).eval₁ x` to `0`, a value.
- `n = 0`: `constZeroCircuit 0` is well-formed (`nodes 0 = Fin 0`) and the family
  still decides correctly at length `0`, since `ε ∈ L` routes to `allOnesCircuit 0`,
  which accepts, and `ε ∉ L` routes to `constZeroCircuit 0`, which rejects.
- Style (Advisory 11): one import, no `set_option`, no copyright header — matching
  `PPoly.lean` and `SizeClasses.lean`, its two immediate neighbours.
- Aggregator: `TCSlib/Complexity/CircuitComplexity.lean` imports the module and its
  `## Contents` entry describes it accurately.

Verdict: **REVISE** — two Blocking, both duplicated-prose defects under Blocking 7.
No Lean code needs to change and no proof obligation is outstanding; the mathematics,
the axiom profile and the faithfulness to Claim 6.8 are all sound. U2 stays `WIP` in
`ch6/PLAN.md`.

## U2 — round 2 — PASS

Independent verification. `lake build TCSlib.Complexity.CircuitComplexity` exits 0,
**3029 jobs**, no errors or warnings — matching the claim exactly. `#print axioms`
run by me on all 17 public declarations: sixteen are
`[propext, Classical.choice, Quot.sound]` and `ACP.notGateOp` is `[propext]` alone,
as claimed; no `sorryAx` anywhere. `#check_failure ACP.constZeroNodes` still fails,
so the private def stays inaccessible. `grep -c sorry` = **0**. **176** lines,
**104** code, module docstring lines 3–31 = **29**, all **18** declarations carry a
docstring (checked mechanically). No line exceeds 100 columns. Every figure in the
report is reproducible.

### Round 1 Blocking findings — both resolved, dropped

- :67 `constZeroNodes`'s docstring is now "The three layers of `constZeroCircuit n`:
  the `n` inputs, then two singleton layers." It names no gate and restates nothing
  from the Design block, and it is now the exact shape of U1's surviving
  `allOnesNodes` (SizeClasses.lean:76). Resolved.
- :11 the `## Main results` bullet is now "`ACP.unaryFamily` — Claim 6.8's circuit
  family for a unary `L`." — a label. The branching definition survives only at
  :111–112, where it belongs. Resolved. The :10 bullet was left as it was, which is
  correct: it was always label-length and I flagged it only as a lesser instance.
  The new :12 bullet for `inSIZE_two_of_le_allOnes` overlaps its declaration
  docstring (:167) no more than U1's `_inSIZE_linear` bullet overlaps its own, which
  passed; no new finding.

### Round 1 Advisory findings — all four resolved, dropped

- :22 now names `Classical.propDecidable`, which is what `#print` with `pp.all`
  showed the term actually carries.
- :18 now reads "the two it uses", which is true of `constZeroCircuit` and no longer
  says anything false about `AC_GateOps`.
- :12 `Language.inSIZE_two_of_le_allOnes` added to `## Main results`.
- :88 the `show` was rewritten. See the correction below.

### Correction: my round 1 Advisory on `constZeroCircuit_eval₁` was half wrong

The formalizer pushed back and it is right. I re-ran the probes:

| probe | result |
|---|---|
| `:= rfl` (term mode, expected type present) | **fails** — `Type mismatch: rfl has type ?m = ?m` |
| `:= Eq.refl _` | **fails**, same way |
| `:= by rfl` (tactic, **no** `show`) | **fails** — "`rfl` failed: the left-hand side `(constZeroCircuit n).eval₁ x` is not definitionally equal to the right-hand side `0`" |
| `:= by show (1 : Fin 2) - 1 = 0; rfl` | **closes** |

So the `show` is **load-bearing, not decoration**, and my round 1 suggestion that it
could be replaced by a bare `rfl` was wrong. Probe 3 is the decisive one: the tactic
`rfl` has the goal in hand and still fails, which also rules out the formalizer's own
explanation ("reducible-transparency elaboration has no expected type to drive
unification") — Lean prints the expected type in the term-mode error, so it plainly
had one. The actual mechanism: `rfl` needs `isDefEq lhs rhs` for `lhs` and `rhs`
exactly as given, and here `lhs` is `eval₁` of a `Nat.recAux` over a `Fin`-indexed
motive carrying proof arguments while `rhs` is `(0 : Fin 2)` = `OfNat.ofNat 0`. The
unifier will not drive that reduction unprompted. `show` splits the one unification
it refuses into two it accepts: `goal =?= (1 : Fin 2) - 1 = 0`, then the trivial
`1 - 1 = 0`. The right conclusion is that the `show` is the mechanism, not a
readability flourish.

**Both `1`s are genuinely operative — this is not round 1's decoration renumbered.**
I checked by perturbing each position independently:

- `show (0 : Fin 2) - 1 = 0` — **rejected**: "pattern `0 - 1 = 0` is not
  definitionally equal to target". So the left `1` is pinned by `notGateOp`'s
  `fun x => 1 - x 0`.
- `show (1 : Fin 2) - 0 = 0` — **rejected** likewise. So the right `1` is pinned by
  the value of the empty `AND`.

That is precisely the defect the round 1 Advisory identified, and it is gone. In
round 1 the `(1 : Fin 2)` sat inside `∏ _i : Fin 0, _`, a vacuous position where I
verified `(0 : Fin 2)` and `(37 : Fin 2)` were accepted just as happily; the term
shown to the reader carried no information. Now every literal in the `show` is
forced, and a reader who mistrusts it can falsify it by changing one character.
The finding was correct about the misleading displayed term and wrong about the
technique being removable; the fix addressed the part that was correct.

### The line-count convention — the round 1 "wrong split" was no such thing

I could not run "the exact `awk` command it now uses": the command was not included
in the message relayed to me and appears nowhere in `ch6/`. Someone should paste it
into `ch6/REVIEW_CRITERIA.md`, which is not mine to edit. What I did instead was
settle the underlying question, and the answer retires the dispute for every unit.

The two figures are the same file counted two ways, differing only over blank lines
that fall *inside* a `/-! ... -/` block:

```sh
# convention A — a blank line inside a block comment is part of the comment
awk '
  /^[[:space:]]*$/ && !inb { blank++; next }
  inb { comment++; if (/-\//) inb=0; next }
  /^[[:space:]]*\/-/ { comment++; if (!/-\//) inb=1; next }
  /^[[:space:]]*--/ { comment++; next }
  { code++ }
  END { printf "total=%d code=%d comment=%d blank=%d\n", NR, code, comment, blank }
' <file>
# → total=176 code=104 comment=50 blank=22

# convention B — a blank line is blank wherever it occurs  (what I used in round 1)
awk '
  inb { if (/^[[:space:]]*$/) blank++; else comment++; if (/-\//) inb=0; next }
  /^[[:space:]]*$/ { blank++; next }
  /^[[:space:]]*\/-/ { comment++; if (!/-\//) inb=1; next }
  /^[[:space:]]*--/ { comment++; next }
  { code++ }
  END { printf "total=%d code=%d comment=%d blank=%d\n", NR, code, comment, blank }
' <file>
# → total=176 code=104 comment=43 blank=29
```

Both ran by me just now on `UnaryLanguages.lean`. `50 + 22 = 43 + 29 = 72`, and
`code = 104` either way. So U2 round 1's "50 comment / 22 blank" was **convention A
applied correctly**, not a miscount, and I should have written it that way rather
than listing it among the report's errors — round 1's own log already noticed the
arithmetic identity without drawing the conclusion. I withdraw the implication that
the formalizer counted wrong. The only thing that was ever wrong in that report was
the job count.

Recommendation for `ch6/REVIEW_CRITERIA.md`, for the coordinator to apply: paste in
**convention A** and make it the shared counter, so Blocking 7's "comment must not
exceed code" is checked against one number across all units. A is the stricter of the
two — it attributes 50 comment lines to this file where B attributes 43, so every
file that passes A passes B but not conversely — and Blocking 7 exists to hold the
line on docstring bloat, so the stricter reading is the one that serves it. Either
convention is defensible; what matters is that exactly one is written down. I have
not edited `REVIEW_CRITERIA.md`, which is not mine under the ownership rule.

### Re-checked and still clear

- The mathematics is untouched from round 1: the only Lean change is
  `constZeroCircuit_eval₁`'s proof, and its statement, its `@[simp]` attribute and
  its axiom profile are unchanged. Round 1's semantic checks therefore still stand —
  `Leven := {w ∈ allOnes | Even w.length}` is in `P/poly`, the family accepts
  `[true,true]`, rejects `[true]`, and its language is not `Set.univ`; the degenerate
  ends `(fun _ => False)` and `Language.allOnes` both go through; `size = 2 > 0`, so
  the `Nat.card` trap is avoided.
- All six round 1 rulings stand unchanged: the `≤`-for-`⊆` deviation is forced,
  adequate and recorded (:25–26); `Language.exists_le_allOnes` is U2's to own and
  U4's to consume; the non-uniformity is recorded as content rather than defect and
  the `if_pos`/`if_neg` route is instance-agnostic; the size-`2`-for-linear
  strengthening is recorded with no overclaim; `notGateOp`'s docstring does not
  misdescribe, and its duplication of `ACpGates.lean:29` remains a deferred
  follow-up, now recorded in `ch6/PLAN.md` for both gates.
- The namespace boundary — `ACP` for every declaration whose statement mentions a
  circuit, `Language` for every one that does not — is still honoured exactly.

Verdict: **PASS** — zero Blocking. U2 flipped to `DONE` in `ch6/PLAN.md`, which
releases U4.

## U4 — round 1 — PASS

Independent verification, all figures reproduced by me, none taken from the report.

- `lake build TCSlib.Complexity.CircuitComplexity.UHalt` → exit 0, **3027 jobs**,
  no errors, no warnings. Matches the claim exactly.
- `lake build TCSlib.Complexity.CircuitComplexity` (the aggregator, which now
  pulls in Basic, Formulas, DecisionTree, PPoly, CircuitSat, UnaryLanguages,
  UHalt, SizeClasses) → exit 0, **3036 jobs**, no errors, no warnings. The five
  Ch.6 units build together.
- `grep -c sorry TCSlib/Complexity/CircuitComplexity/UHalt.lean` = **0**. The word
  does not occur even in prose.
- Blocking 7, measured with the mandated `awk` command verbatim:
  `total=103 code=46 comment=40 blank=17`. Comment 40 < code 46, so the file is
  not more comment than code. Module docstring is lines 4–30 = **27** lines,
  under the ~40 cap. Every figure in the report reproduces.
- All **12** declarations carry a docstring (checked mechanically by scanning the
  line preceding each `def`/`theorem`): `haltingSet`(:36),
  `not_computablePred_mem_haltingSet`(:40), `unary`(:55), `mem_unary_iff`(:58),
  `unary_le_allOnes`(:62), `replicate_mem_unary_iff`(:65), `unary_inPPoly`(:71),
  `not_computablePred_mem_unary`(:75), `uhalt`(:89), `uhalt_inPPoly`(:92),
  `not_computablePred_mem_uhalt`(:95), `exists_inPPoly_not_computablePred`(:99).
- `#print axioms` run by me on all 12: `Language.unary` and `Language.mem_unary_iff`
  depend on no axioms, `Language.replicate_mem_unary_iff` on `[propext]`, the other
  nine on `[propext, Classical.choice, Quot.sound]`. **No `sorryAx` anywhere.**
- No line exceeds 100 columns.

### Ruling on the encoding swap — `Language.uhalt` does deserve the name, and the docstring does not overclaim

This is the question the round turned on, and the answer is that the file is clean.

AB p.110 (PDF p.136), verified by me with `pdftotext -f 136 -l 136`, reads
`UHALT = {1ⁿ : n's binary expansion encodes a pair ⟨M, x⟩ such that M halts on
input x}`. The module docstring at :18–19 quotes that sentence verbatim — I
checked it word for word against the extracted page, including "binary expansion"
and "halts on input x". `uhalt` (:89) is instead `unary haltingSet` with
`haltingSet = {n | (eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2).Dom}`.

Two reasons this is a legitimate divergence and not a mislabelled object.

**1. AB's UHALT is itself only defined up to a numbering.** AB never pins down how
a binary expansion encodes `⟨M, x⟩` — no pairing function, no TM encoding, nothing.
`PLAN.md` U4 anticipated exactly this ("may be obtainable ... without building AB's
explicit `⟨M, x⟩` encoding — look first"), and it is the same reason Example 6.3
part 2 was SKIPped. So there is no fixed set of strings that "AB's UHALT" names and
that this file could have failed to hit. What AB fixes is the *shape*: unary, with
membership of `1ⁿ` determined by decoding `n` to an index/input pair and asking
whether the indexed machine halts. `Nat.unpair` is a computable bijection
`ℕ ≃ ℕ × ℕ` and `Denumerable.ofNat Nat.Partrec.Code` is a computable enumeration of
a universal model, so the file instantiates that shape with a numbering that is
recursively isomorphic to any AB could have chosen.

**2. Every property AB uses is preserved, which is what Blocking 2's
"class-preserving" asks.** AB uses exactly two facts about UHALT — it is unary, and
it is undecidable — and both are theorems here (`unary_le_allOnes`, :62, applied at
:101; `not_computablePred_mem_uhalt`, :95). Nothing downstream in AB's argument
reads the encoding.

**The docstring asserts no more than that.** :19 says "The numbering is changed, the
shape kept" and then spells out the replacement mechanism in full (:20–24), under an
explicit `## Divergences from Arora–Barak p.110` heading. That is the disclosure
Blocking 2 demands, made once in the module block, which is where Blocking 7 says it
must live and where it must *only* live. The bare "Arora–Barak's `UHALT`" at :88 and
"AB's `UHALT`" at :13 are therefore not overclaims: they are scoped by the divergence
section seven lines above, and restating the caveat on the declaration would itself
have been the Blocking-7 defect this loop has caught four times. I looked for the
round-1-through-4 pattern (a docstring asserting more or other than the code does) on
all twelve declarations and the module block, line by line, and did not find it.

I also checked the statement is not vacuous, in Lean rather than by inspection:
- `Language.unary ∅ = ⊥` and `Language.unary Set.univ = Language.allOnes` — both
  proved, so `unary` is neither constantly empty nor constantly everything.
- `Nat.Partrec.Code.haltingSet ≠ Set.univ` (else the constant-`true` predicate would
  decide it, contradicting :40) and
  `Nat.pair (encode (Code.const 0)) 0 ∈ haltingSet` (that code halts on `0`).
- Hence `Language.uhalt ≠ ⊥`, `Language.uhalt ≠ ⊤` (`[false] ∉ uhalt`, via
  `unary_le_allOnes`), and — the one that actually matters —
  **`Language.uhalt ≠ Language.allOnes`**. So `uhalt` is a *proper, non-trivial*
  subset of the all-ones words, not the degenerate unary language that would make
  `exists_inPPoly_not_computablePred` cheap.

### Scope boundary — honest, and the missing half is named

The file defines no `P`, no machine model and no time-bounded class (grepped for
`Turing`, `TM`, `class P`, `def P`, `InP`, `⊊` — the only hit is the prose at :26),
and nowhere claims `P ⊊ P/poly`. :26–29 states AB's conclusion, says why it is not
available (no machine model, no class `P`), names the *other* missing ingredient
(Theorem 6.6, deferred as `PLAN.md` U5), and then says precisely which half is
delivered: "some unary language is in `P/poly` and is not computable". I checked that
against `exists_inPPoly_not_computablePred` (:99–101) and it is exact. This satisfies
the standing convention "`P` is not ours to define".

### The four flagged points — judged

**1. `haltingSet` in `Nat.Partrec.Code` rather than `Language` — the deviation is
right.** The U1 ruling (logged above, "Ruling on the namespace split") is stated as
"`ACP` holds every declaration whose statement mentions a circuit, `Language` holds
every one that does not". Read as a universal law it would put `haltingSet` in
`Language`, but it was written to describe a two-way split between *circuit-level*
and *language-level* declarations in `SizeClasses.lean`, and `haltingSet : Set ℕ` is
neither: it is not a `Language` at all. Mathlib's actual rule — namespace follows the
head symbol of the subject — puts it with `Nat.Partrec.Code.eval`, which is the only
constant its body mentions. And `Language.haltingSet : Set ℕ` would enable the
dot-notation `L.haltingSet` on a language, which is meaningless. The formalizer's
reason is the correct one. No finding.

**2. `Language.unary`'s generality — pre-authorized, and I verified the
authorization rather than taking it.** U2 round 1, ruling 3, in this log, reads:
"U4 should *consume* it, and when it needs to name the language rather than assert it
exists, introduce `Language.unary` there — not retrofit it here on speculation
(Advisory 9)." That is verbatim what U4 did. Defining `uhalt` directly would also
have been worse: `not_computablePred_mem_unary` (:75) is the reduction `n ↦ 1ⁿ`, which
has nothing to do with halting, and inlining it into a `uhalt`-specific proof would
hide a general fact inside a special case. No finding.

**3. The `L ≤ allOnes` conjunct in `exists_inPPoly_not_computablePred` is right.**
AB's sentence is "there are unary languages that are undecidable ... whereas every
unary language is in `P/poly`" — the whole force of the argument is that the witness
is *unary*, because that is what makes Claim 6.8 apply. Dropping the conjunct for the
weaker `∃ L, L.InPPoly ∧ ¬ComputablePred (· ∈ L)` would state something true but
strictly less than AB's sentence, and would lose the only reason the witness is
easy to produce. Keep it. No finding.

**4. `hrep` stays inline — agreed, and for a reason I checked.** The repo's
have→lemma rule requires a have to be *all* of: nontrivial body, meaningful outside
its proof, reusable, clean interface. `hrep`'s body is a single term (:79–81), so it
fails the first clause, and Advisory 9 forbids lifting on a single use. I did check
whether it duplicates something upstream, since that would have made it a Blocking 4
reuse defect: `exact?` on `Computable fun n : ℕ => List.replicate n true` fails, and
`grep` over all of `Mathlib/` for `Primrec.*replicate` returns nothing. So the fact
is genuinely absent from Mathlib, it is not duplicated, and one use does not earn a
lemma. If a second consumer appears its home is upstream, not here. No finding.

**5. The "AB Claim 6.8" citation resolves — chain verified end to end.**
`uhalt_inPPoly` (:92) `:= unary_inPPoly _`; `unary_inPPoly` (:71)
`:= inPPoly_of_le_allOnes (unary_le_allOnes S)`; `Language.inPPoly_of_le_allOnes`
(`UnaryLanguages.lean:174`) carries the docstring "AB Claim 6.8: every unary language
is in `P/poly`"; and AB p.110, in the text I extracted, reads "Claim 6.8 Let
L ⊆ {0,1}* be a unary language (i.e., L ⊆ {1ⁿ : n ∈ N}). Then, L ∈ P/poly." The
number, the page and the content all match. This is not a repeat of the U3 round 1
false-citation defect. No finding.

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/UHalt.lean:7 — the `## Main results`
  list omits `Language.uhalt_inPPoly` (:92) and `Language.not_computablePred_mem_uhalt`
  (:95), which are the two facts the module *title* advertises ("an undecidable unary
  language in `P/poly`"). The list names the `unary`-level lemmas but not their `uhalt`
  instances, so a reader scanning the header cannot find the names of the results the
  title promises. (Same shape as the U1 round 2 advisory on `Language.allOnes`.)
  → add the two lines.
- [Advisory] TCSlib/Complexity/CircuitComplexity/UHalt.lean:99 — the name
  `exists_inPPoly_not_computablePred` omits the `L ≤ allOnes` conjunct the statement
  carries, so under Blocking 5 ("named after what they say") the name is weaker than
  the theorem. Ruling 3 above keeps the conjunct, which makes the name the thing to
  change, not the statement. → `exists_le_allOnes_inPPoly_not_computablePred`; the
  `exists_le_allOnes` prefix is already established in this namespace by
  `UnaryLanguages.lean:45`.
- [Advisory] TCSlib/Complexity/CircuitComplexity/UHalt.lean:19 — "The numbering is
  changed, the shape kept" understates the change by one step: AB's `M` is a Turing
  machine, whereas here the first component numbers a `Nat.Partrec.Code`, so the
  universal model changes as well as the numbering. The very next clause (:20–21) names
  `Denumerable.ofNat Nat.Partrec.Code` explicitly, so nothing is concealed and the
  sentence as a whole is accurate — this is the one wording I weighed for Blocking and
  did not promote, because the colon makes the mechanism part of the claim and because
  TM indices and `Code` indices are related by a computable bijection, which is what
  "change of numbering" means. → optionally "The numbering and the universal model are
  changed, the shape kept".
- [Advisory] TCSlib/Complexity/CircuitComplexity/UHalt.lean:91 — "by AB Claim 6.8"
  repeats the attribution already carried by `unary_inPPoly`'s docstring at :70, which
  is the declaration that actually invokes `inPPoly_of_le_allOnes`. Not the Blocking 7
  defect (a citation is not a module-block design decision, and both are correct), but
  "`UHALT` is in `P/poly`." alone would be exact and one word shorter than the rule's
  budget. → drop the clause.

### Checked and cleared (no finding)

- Blocking 4, reuse: nothing is redefined. `Language.allOnes`, `mem_allOnes_iff`,
  `inPPoly_of_le_allOnes` come from U1/U2; `ComputablePred`, `ComputablePred.computable_iff`,
  `ComputablePred.halting_problem`, `Nat.Partrec.Code.eval`, `Primrec.list_map`,
  `Primrec.list_range`, `Primrec₂.natPair` come from Mathlib. Mathlib has no
  `haltingSet : Set ℕ` (only `halting_problem`, stated over `Code` at
  `Mathlib/Computability/Halting.lean:249`), and `grep` over `TCSlib/` finds no other
  `unary` language definition.
- Blocking 5, naming: `haltingSet`, `unary`, `uhalt` are lowerCamelCase data defs;
  `mem_unary_iff`, `replicate_mem_unary_iff`, `unary_le_allOnes`, `unary_inPPoly`,
  `uhalt_inPPoly`, `not_computablePred_mem_unary`, `not_computablePred_mem_uhalt`,
  `not_computablePred_mem_haltingSet` are snake_case and each says what it states.
  The one gap is the advisory at :99.
- The proof of `not_computablePred_mem_haltingSet` (:40–48) is a genuine reduction,
  not a restatement: it decides `fun c => (eval c 0).Dom` from a decider for
  `haltingSet` by feeding `Nat.pair (encode c) 0`, and lands on Mathlib's
  `ComputablePred.halting_problem 0`. `Nat.unpair_pair` and `Denumerable.ofNat_encode`
  are what make the two agree; I traced it and it is sound.
- Advisory 8: no `@[simp]` is declared in this file at all.
- Advisory 10: the two real proofs are short and structured (`obtain` / `refine` /
  `funext`), with no `simp_all` chain. The only `simpa` (:48) closes a defeq step.
- Advisory 11, style: two imports at the granularity of the neighbours,
  no `set_option`, no copyright header — matching `PPoly.lean`, `SizeClasses.lean` and
  `UnaryLanguages.lean`. (`CircuitSat.lean` has a header, but it has a different author.)
- Aggregator: `TCSlib/Complexity/CircuitComplexity.lean` imports the module (line 7)
  and its `## Contents` entry describes it accurately, including the "`P ⊊ P/poly`
  itself is not stated: TCSlib has no `P`" caveat.

### Cross-track item — confirmed, not a suggestion

`Language.exists_le_allOnes` (`UnaryLanguages.lean:45`) **is** subsumed by U4's
`Language.unary` and its API, and I verified this in Lean rather than by eye:

- `Language.unary S = {w : List Bool | w ∈ Language.allOnes ∧ w.length ∈ S}` holds by
  `rfl` — `unary`'s body (`UHalt.lean:55`) is *literally* the set that
  `exists_le_allOnes` builds inline at `UnaryLanguages.lean:48`, not merely an
  equivalent one.
- The whole of `exists_le_allOnes` is then
  `fun S => ⟨Language.unary S, Language.unary_le_allOnes S, fun n => Language.replicate_mem_unary_iff n⟩`,
  which typechecks. Its seven-line tactic proof (`UnaryLanguages.lean:48–54`)
  re-derives `unary_le_allOnes` and `replicate_mem_unary_iff` inline.

Recommendation for the cross-track pass: either reduce `exists_le_allOnes` to that
one-line term, or drop it and have its consumers use `Language.unary` directly. It
cannot be done from `UHalt.lean` (wrong file, and `UnaryLanguages` is imported *by*
`UHalt`, so `unary` would have to move up to `UnaryLanguages.lean`). Also worth noting
while the pass is open: `Language.allOnes = Language.unary Set.univ` is provable
(by `ext`, not by `rfl`), so the two definitions overlap at one point.

Verdict: **PASS** — zero Blocking, four Advisory. The encoding swap is a recorded,
class-preserving divergence and the docstring claims exactly it and no more; the
scope boundary names the missing half and its two missing ingredients; the language
is provably non-degenerate at both ends. U4 flipped to `DONE` in `ch6/PLAN.md`,
completing every unit in the plan.

## U6+U7 — round 1 — REVISE

Two Blocking. Everything U7 self-reported as measured reproduces; the citation
work, the sketches and the `autoImplicit` migration are all sound. The two
findings are both in prose, and one of them is the loop's recurring defect
landing in the single comment whose entire purpose was to make a policy
deviation auditable.

### Independent verification (nothing below taken from the report)

- `lake build TCSlib.Complexity.CircuitComplexity` → exit 0, **3033 jobs**.
  Claim reproduces exactly.
- `lake build` (full) → exit 0, **3690 jobs**. Claim reproduces exactly. The
  tree is not warning-free, but every warning is outside these nine files
  (`ErrorCorrectingCodes/MRRW.lean` ×7 `declaration uses 'sorry'`,
  `LMN/IterativeReduction.lean:214` `declaration uses 'sorry'`,
  `LearningTheory/Hedge.lean`, `ListDecoding.lean`, `Rademacher.lean`), all
  pre-existing and none of them ours.
- `zsh scripts/lean_check.sh` on all nine → exit 0, **0 errors, 0 warnings** on
  each.
- `#print axioms`: I enumerated declarations mechanically rather than trusting a
  list, and checked **142** (not the 51 claimed — the report undercounted its own
  coverage). Zero `sorryAx`. 93 are `[propext, Classical.choice, Quot.sound]`,
  6 `[propext, Quot.sound]`, 5 `[propext]`, 33 depend on no axioms. The 14 names
  my scanner could not resolve are all accounted for: 7 `private` declarations
  (`foldr_and_map`, `foldr_or_map`, `foldr_add_map`, `foldr_add_map_le`,
  `allOnesNodes`, `constZeroNodes`, `finTwoEquiv_symm_eq_one_iff`), 5 under the
  nested `ACP.CircuitFamily` namespace (re-checked with the full prefix, all
  clean), and 2 scanner false positives from prose.
- Docstring coverage (Blocking 6): complete. Every declaration in all nine files
  carries one; the seven my scanner flagged each have an `@[simp]` between the
  docstring and the declaration.
- No line exceeds 100 columns in any of the nine.
- AB tags spot-checked against the PDF (`pdftotext -f 136 -l 137`): "Claim 6.8",
  "Definition 6.9 (Circuit satisfiability or CKT-SAT)", "Lemma 6.11 CKT-SAT ≤p
  3SAT", and the `UHALT` sentence all read as cited.

Per-file `awk`, the mandated command verbatim:

```
CircuitComplexity.lean         total=56  code=8   comment=47  blank=1
CircuitComplexity/Basic.lean            total=528 code=282 comment=185 blank=61
CircuitComplexity/Formulas.lean         total=92  code=24  comment=53  blank=15
CircuitComplexity/DecisionTree.lean     total=184 code=94  comment=78  blank=12
CircuitComplexity/PPoly.lean            total=139 code=47  comment=71  blank=21
CircuitComplexity/SizeClasses.lean      total=162 code=76  comment=62  blank=24
CircuitComplexity/UnaryLanguages.lean   total=220 code=112 comment=81  blank=27
CircuitComplexity/CircuitSat.lean       total=402 code=231 comment=138 blank=33
CircuitComplexity/UHalt.lean            total=107 code=41  comment=52  blank=14
```

The `code` figure agrees with the report on all four files it tabulated
(8 / 24 / 47 / 41), and exactly those four are the ones with comment > code.
The claim that only four files exceed the ratio reproduces.

### PRIORITY 1 — the `[OD14]` attributions are genuine

I opened `blueprint/src/references/boolean-ch03-spectral-learning-restrictions.md`
and `boolean-ch04-dnf-switching-lmn.md` and checked every numbered definition
against the Lean. **Every citation is real, correctly numbered, and correctly
sectioned.** This is not a repeat of the U3 round-1 false-citation defect.

| Lean | Tag | Source text | |
|---|---|---|---|
| `Literal` / `Term` / `DNF` (`Formulas.lean:50,60,70`) | Def 4.1 | ch04:18 — "a logical OR of terms, each a logical AND of literals. A literal is either `x_i` or its negation" | ✓ |
| `Term.width` (`Formulas.lean:63`) | Def 4.1 | ch04:18 — "The number of literals in a term is its width" | ✓ |
| `DNF.width` (`Formulas.lean:73`) | Def 4.3 | ch04:32 — "its width is the maximum width of its terms" | ✓ |
| `CNF` / `CNF.width` (`Formulas.lean:81,84`) | Def 4.4 | ch04:40 — "a logical AND of clauses… Size and width are defined as for DNFs" | ✓ |
| `DecisionTree` (`DecisionTree.lean:65`) | Def 3.13 | ch03:121 — verbatim match | ✓ |
| `depth` / `dtDepth` (`DecisionTree.lean:75,179`) | §3.2 | ch03:57 is "## 3.2. Subspaces and decision trees"; depth and `DT(f)` are defined in *unnumbered* prose at ch03:126, so §3.2 is the only citable locus | ✓ |
| `NAndCircuit` / `NOrCircuit` (`Basic.lean:186,193`) | Def 4.26 | ch04:308 — "Gates in odd layers use one connective (∧ or ∨), and gates in even layers use the other" | ✓ |
| `Nodup` base invariant (`Basic.lean:187,194`) | Def 4.27 | ch04:312 — "No layer-1 node is connected to a variable or its negation more than once". `(lits.map Lit.idx).Nodup` forbids a repeated **index**, hence both `x_i` twice and `x_i` with `¬x_i` — an exact rendering, not an approximation | ✓ |
| `## Divergences from [OD14, §4.5]` (`Basic.lean:41`) | §4.5 | ch04:294 is "## 4.5. Highlight: LMN's work on constant-depth circuits"; Defs 4.26/4.27 sit at 308/312, inside it | ✓ |
| `## Divergences from [OD14, §4.1]` (`Formulas.lean:27`) | §4.1 | ch04:14; Defs 4.1/4.3/4.4 at 18/32/40, inside it | ✓ |

All three self-reported divergences check out, and each is a real difference, not
a hedge:

1. `Formulas.lean:29-30` — "a `Term` … may hold both a variable and its
   negation, which [OD14, Def 4.1] forbids". Def 4.1 (ch04:18) does say "No term
   contains both a variable and its negation"; `Term` is `List (Literal n)` with
   no constraint. **Correct.**
2. `DecisionTree.lean:38-40` — "[OD14, Def 3.13] labels leaves by reals and
   forbids a coordinate from being queried twice". Def 3.13 (ch03:121) says
   "leaves have real labels, and no coordinate repeats on a root-to-leaf path";
   `DecisionTree` has `| leaf (val : Bool)` and no path condition. **Correct.**
3. `Basic.lean:45-47` — "`size` counts every node, leaves included, where
   [OD14, Def 4.27] counts only the internal layers". Def 4.27 (ch04:312) is
   "the number of nodes in layers 1 through d−1", excluding input layer 0 *and*
   output layer d; `Circuit.size` (`Basic.lean:158`) is `1 +` the children's
   total with `| .lit _ => 1`. **Correct**, and "internal layers" is the precise
   word for layers 1..d−1.

Leaving `Circuit` itself untagged (`Basic.lean:99`) is also right, and the stated
reason ("[OD14]'s circuits are DAGs", `Basic.lean:48`) holds: Def 4.26 is a
layered DAG with forced alternation, `Circuit` is an unconstrained tree with
neither. It matches no numbered definition. **Verified — no tag was manufactured
and none was withheld that was owed.**

### PRIORITY 2 — all 10 proof sketches describe what the code does

Ten sketches, ten proofs, checked line by line against policy §3's requirement
that named steps be visible as `have`s or lemmas. All pass. The three specific
claims:

- `Circuit.tseitin_length_lt` (`CircuitSat.lean:372`). The sketch's "the
  induction therefore goes through a strengthened statement about lists, proved
  by a side induction: the children's own clauses *together with one extra clause
  per child* still fit inside three times the children's total size" is the
  `hlist` `have` at :377-380, which states exactly
  `(ds.flatMap fun d => d.tseitin).length + ds.length ≤ 3 * ds.foldr (…) 0`.
  The `+ ds.length` is the "one extra clause per child". The sketch's next step,
  "the gate's own contribution is exactly one clause per child plus the long
  clause", is `hg` at :391. **Exact.**
- `eval_node_iff_of_gateClauses` (`CircuitSat.lean:238`). The "two facts" are
  `hmain` and `hside`, at :243/:247 (OR case) and :259/:263 (AND case). The
  sketch's "from the long clause… and from the short clauses, one per child"
  maps onto them in that order: `hmain` is read off the head clause,
  `hside` is `∀ c ∈ cs` read off the mapped clauses. **Exact.**
- `toNAnd_toNOr_litCount`'s `by_contra`/`revert` opener (`Basic.lean:383-384`).
  **U7's call was right, and I confirmed it by reading the proof.** `by_contra h`
  followed immediately by `revert h` turns goal `P` into `¬P → False` and
  derives nothing from the negation — it is not a contradiction argument, and
  describing it as one would have misled. The proof is the structural induction
  the sketch describes, with the `h_foldr` side inductions at :395 and :403
  that the sketch's last sentence names. One correction to the framing: the two
  lines are *not removable* — deleting them and rebuilding gives
  `simp_all made no progress` twice at :386. They are load-bearing for the
  tactic script (they reshape the induction motive) while contributing nothing
  mathematically. "Vacuous" is the wrong word; "mathematically inert" is right.
  The editorial decision stands either way.

Also confirmed mechanically that no proof over ~20 tactic lines lacks a sketch.

### PRIORITY 3 — the `autoImplicit false` migration is safe

Re-verified from scratch, and on **48** declarations rather than the 40 claimed
(I enumerated them from the file instead of trusting the list). Method: built
the post-edit file as-is, and a reconstructed pre-edit file with
`set_option autoImplicit true`, `set_option relaxedAutoImplicit true` and the
`variable {n : Nat}` line at :72 deleted; appended the same 48 `#check (@…)`
lines to both; compiled both with `lake env lean` (both exit 0) and diffed the
output.

**`diff` is empty. All 48 signatures are byte-identical.** No theorem says
anything different. The one-line `variable` fix is equivalent to editing the 30
signatures, and the claim is true.

### Blocking

- [Blocking] TCSlib/Complexity/CircuitComplexity/Basic.lean:14 — the
  `-- POLICY EXCEPTION` comment claims `Real.rpow_natCast`
  (`LMN/BernoulliCost.lean`) "reach[es] them through here". It does not:
  **`BernoulliCost.lean` has no import path to `Basic.lean` at all.** Its TCSlib
  closure is `Switching.BernoulliRestriction → Switching.Restriction →
  {Formulas, DecisionTree}`. Line 11-12's "`TCSlib/BooleanAnalysis/LMN/*` and
  `Switching/*` import this file" is false about `Switching/*` for the same
  reason: **no** module under `TCSlib/BooleanAnalysis/Switching/` reaches
  `Basic.lean` (20 under `LMN/` do).

  Proved twice over, not by inspection. (a) Transitive import closure, computed
  per module. (b) Trim experiments, which is the check the unit was asked for:
  deleting `import Mathlib.Tactic` from **`DecisionTree.lean`** and running a
  full `lake build` fails at
  `LMN/BernoulliCost.lean:176:27: Unknown constant 'Real.rpow_natCast'` — the
  example this comment claims for `Basic.lean`. Deleting it from
  **`Basic.lean`** fails somewhere else entirely:
  `LMN/NormalFormConversion.lean:144:22: Invalid field 'forall': The environment
  does not contain 'List.Pairwise.forall'` — a file the comment never names,
  and which is the *cleanest* case of the rule it is trying to state, since
  `NormalFormConversion.lean` imports `Basic` and `Formulas` and nothing else.

  The comment is a verbatim copy of `DecisionTree.lean:8-13`, where all of it is
  true. Pasted into `Basic.lean` two of its factual claims become false and the
  one dependent that actually bites goes unmentioned. This is round 1-4's
  recurring defect — prose asserting other than what the code does — landing in
  the one comment whose whole job is to let the next reader audit a deliberate
  policy deviation. Someone who trims this import and goes looking for
  `BernoulliCost` will find no connection and conclude the exception was bogus.
  → in `Basic.lean` name `LMN/NormalFormConversion.lean` (`List.Pairwise.forall`)
  and drop `Switching/*` and the `BernoulliCost` example; keep that example only
  in `DecisionTree.lean`, where the trim proves it.

- [Blocking] TCSlib/Complexity/CircuitComplexity/SizeClasses.lean:61 —
  `finTwoEquiv_symm_eq_one_iff`'s docstring is "``finTwoEquiv`` sends `true`, and
  only `true`, to `1`.  `private`, so that the root namespace carries nothing
  from this file." The second sentence argues the design choice instead of
  stating what the lemma is — Blocking 7's "say what the thing *is*, and stop"
  and "reject on … any docstring that argues a point instead of stating a fact".
  Same shape as the two findings already recorded against this file at U1 round 1
  (:122 and :135). The assertion is *true* — I checked, every other declaration
  here is under `Language.` or `ACP.` — but `private` is self-documenting and the
  reason belongs in the module block or nowhere. → cut the second sentence.

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/UHalt.lean:73-75 —
  **answering U6's third open question: yes, `Language.unary_inPPoly` should
  follow `unary` into `UnaryLanguages.lean`.** Its body is
  `inPPoly_of_le_allOnes (unary_le_allOnes S)`; all three constants it mentions
  (`unary`, `unary_le_allOnes`, `inPPoly_of_le_allOnes`) now live in
  `UnaryLanguages.lean` at :66, :74 and :218, and it uses nothing from
  `UHalt.lean`. It is tagged `[AB09, Claim 6.8]`, which is `UnaryLanguages.lean`'s
  module *title*, and `UHalt.lean`'s own `## Main results` (:17-23) does not list
  it — a public theorem that neither file's header claims. Policy §1's "helpers
  belong in that area's file, not in the file that first needed them" applies
  directly. Unlike `unary` itself there is no import-direction forcing, which is
  why this is Advisory and not Blocking.
- [Advisory] TCSlib/Complexity/CircuitComplexity/PPoly.lean:9-58 and
  Basic.lean:18-64 — module docstrings run ~45 and ~42 lines after deducting the
  `## References` block, over item 7's ~40 cap. **Not promoted, and item 7 should
  be amended rather than these files trimmed.** Every line over is divergence
  disclosure that Blocking 2 *mandates*, and Blocking 2 names this very file as
  the standard for it ("the way `PPoly.lean` records its fan-in, basis,
  size-measure and layering divergences"). Item 0's exemption list
  (References, source tags, proof sketches) should be extended to `## Divergences`
  for the same reason it covers the other three: policy requires the content.
- [Advisory] TCSlib/Complexity/CircuitComplexity/UHalt.lean — the docstring trim
  inverted the rubric's own precedence. U6's hoist removed ~5 code lines
  (U4 measured `code=46 comment=40`; it is now `code=41 comment=52`), pushing the
  file over the ratio, and U7 responded by cutting prose. Item 0 makes item 7
  yield to policy §2, not the reverse; the correct response was to declare the
  ratio structurally unmeetable here, which is exactly what U7 concluded for the
  other three files. No harm done this time — see the ruling below — but the
  reasoning would cut mandated disclosure next time.
- [Advisory] TCSlib/Complexity/CircuitComplexity.lean:22-44 — the `## Contents`
  list orders the children Basic, Formulas, DecisionTree, PPoly, UnaryLanguages,
  UHalt, CircuitSat, SizeClasses, while the import list at :6-13 orders them
  Basic, Formulas, DecisionTree, PPoly, CircuitSat, UnaryLanguages, UHalt,
  SizeClasses. → match them.

### Rulings on the questions put to this round

**The documented `-- POLICY EXCEPTION` was the right call, and the claimed
failures are real.** I ran the trim myself, twice, on a full `lake build`.
Dropping `import Mathlib.Tactic` from `Basic.lean` fails
(`NormalFormConversion.lean:144`, `List.Pairwise.forall`); dropping it from
`DecisionTree.lean` fails (`BernoulliCost.lean:176`, `Real.rpow_natCast`).
Both exceptions are load-bearing, so failing the unit would have demanded
work in files the unit does not own — `LMN/CircuitReindex.lean` imports
`CircuitComplexity.Basic` and *nothing else*, which I confirmed, so the LMN
track really does route through here. A recorded, auditable exception is the
right instrument. What is not acceptable is that `Basic.lean`'s record is wrong
(Blocking above): the exception's value is entirely in the accuracy of its
justification.

**Agree that the four over-ratio files are structural.** Policy §1 mandates four
docstring sections (`# Title`, `## Main definitions`, `## Main results`,
`## References`) in *every* math file, and §2 adds per-declaration tags. A file
with 8 code lines (the facade, whose `## Contents` list is itself mandated by §1
and whose shape matches the reference example `NPReductions.lean`) or 24
(`Formulas.lean`, twelve definitions and nothing else) cannot fit four sections
plus twelve docstrings under its code count. `UHalt.lean` at 43/41 is two lines
over. `PPoly.lean` at 62/47 is the weakest of the four, but its excess is the
divergence record Blocking 2 requires and holds it up as the exemplar of. The
ratio rule is measuring the wrong thing on small files; it should not be applied
to a facade at all.

**U6's three open items.** (1) The `UHalt.lean` docstring trim: **Blocking 2 still
holds.** I re-checked the surviving `## Divergences from Arora–Barak p.110`
(:25-39) against what U4 endorsed and everything material is still there —
AB's `UHALT` sentence quoted (:27-28), "the numbering is changed, the shape kept"
(:28), the full replacement mechanism (`unpair`,
`Denumerable.ofNat Nat.Partrec.Code`, `Part.Dom` of `eval`, :28-31),
"undecidable" = `¬ ComputablePred` (:31-32), why `haltingSet` sits in
`Nat.Partrec.Code` (:32-33), and the scope boundary naming both missing
ingredients (:35-39). U4's three accepted advisories were all taken:
`## Main results` now lists `uhalt_inPPoly` and `not_computablePred_mem_uhalt`
(:21-22), the rename to `exists_le_allOnes_inPPoly_not_computablePred` landed
(:103) and does carry the conjunct (:104), and the duplicate Claim 6.8 clause at
the old :91 is gone. Nothing endorsed was lost. (2) `Lit.toCktLiteral` is the
**right name**, and the collision was real, not hypothetical:
`BoolCircuit.Lit.toLiteral` already exists at
`LMN/NormalFormConversion.lean:29` as `Lit n → Literal n`, and since `TCSlib.lean`
imports both trees, reusing the name would have been a duplicate declaration at
the root. The target here is `SATTo3SAT.Literal (CktVar n)`, so distinguishing by
the variable type is the informative choice, and `Ckt` is already this file's
established prefix (`CktVar`, `CktSat`). (3) `Language.unary_inPPoly` — see the
Advisory above; it should move.

**`finTwoEquiv_symm_eq_one_iff` as `private` is the right call.** Policy §1 offers
exactly two remedies for root-namespace leakage — "mark internal helpers
`private` or put them in a dedicated inner namespace" — and this is the first.
One use, same file (:145), and U1 round 1's other suggestion (relocate to
`PPoly.lean`) has weakened now that policy forbids the root-namespace option U1
round 2 actually took. Only the docstring is a finding, not the placement.

**U7's four unprompted fixes are all correct.** `PPoly.lean:48` now reads
`## Trap` and describes one trap (`Nat.card` returning `0` on an infinite type),
matching its content. The facade's title `# Circuit Complexity` (:16) matches what
it aggregates. Docstring coverage is complete across all nine files, checked
mechanically. And the self-caught `DecisionTree` overclaim is genuinely repaired:
:41-43 now says `dtDepth` is the least depth "*in that wider class*" and that
"no theorem here relates it to [OD14]'s `DT(f)`" — which is the honest statement,
since `buildFullDTree` witnesses only non-emptiness of the set `Nat.find` searches
(`DecisionTree.lean:179-184`), never minimality. Catching that was the right call
and the replacement wording is exact.

Verdict: **REVISE** — two Blocking, four Advisory. U6 and U7 stay `WIP` in
`ch6/PLAN.md`. Both Blocking items are prose-only; no Lean changes, and no
re-verification of the build, the axioms, the citations, the sketches or the
`autoImplicit` migration will be needed on the next round.

## U6+U7 — round 2 — PASS

Zero Blocking. Both round-1 findings are fixed, and Blocking 1 got a materially
better fix than the one I asked for: rather than correcting a false comment, the
unit ran the controlled experiment, found the import that was actually needed,
and deleted `import Mathlib.Tactic` from `Basic.lean` altogether. One of the two
policy exceptions is gone, not documented.

### Round 1 Blocking — both resolved, dropped

- :14 the false `POLICY EXCEPTION` comment is gone with the import it justified.
  `Basic.lean` now carries `import Mathlib.Data.List.Pairwise` and a five-line
  comment, every claim of which I checked (below). `diff` against my round-1 copy
  of the file shows the import block is the *only* thing that changed: 6 comment
  lines and `import Mathlib.Tactic` out, 5 comment lines and the precise import
  in, `code=282` unchanged.
- :61 `finTwoEquiv_symm_eq_one_iff`'s docstring is now
  "``finTwoEquiv`` sends `true`, and only `true`, to `1`." — the arguing sentence
  cut and nothing else touched. `private` retained, proof (:62-64) unchanged,
  `Language.allOnes` below it unchanged, `code=76` unchanged, file 162 → 161
  lines, `comment` 62 → 61. Exactly one line removed.

### The new comment in `Basic.lean:7-11` — every claim verified, all true

This is the comment that was wrong last round, so I checked it clause by clause
rather than reading it.

- **"Not used below"** — `Pairwise` occurs three times in the file: lines 8 and 9
  (the comment itself) and line 12 (the import). Zero occurrences in the code
  body. ✓
- **"a `List.Nodup` … is a `List.Pairwise`"** — `#print List.Nodup` gives
  `fun {α} => List.Pairwise fun x1 x2 => x1 ≠ x2`. Definitional, not merely
  equivalent; `example (l : List α) : l.Nodup ↔ List.Pairwise (· ≠ ·) l := Iff.rfl`
  compiles. ✓
- **`Mathlib.Data.List.Nodup` does not already supply the API** — a file importing
  only `Mathlib.Data.List.Nodup` and writing `#check @List.Pairwise.forall` fails
  with `Unknown constant 'List.Pairwise.forall'`; the same file importing
  `Mathlib.Data.List.Pairwise` typechecks. So the new import is doing real work and
  is not redundant against the existing one. ✓
- **"`NormalFormConversion.lean` … imports this file and `Formulas.lean`, nothing
  else"** — its import block is exactly those two lines. ✓
- **"reads it back through `List.Pairwise.forall`"** — `NormalFormConversion.lean:144`
  is `exact absurd h_3 ((List.pairwise_map.mp h).forall (fun _ _ hh => hh.symm) h_1 h_2 ha_ne)`.
  The signature `@List.Pairwise.forall : Symmetric R → Pairwise R l → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b`
  matches the call term for term. ✓
- **"46 modules importing this file"** — **46 exactly**, and I reproduce the figure:
  it is the count of modules under `TCSlib/` whose *transitive* import closure
  contains `Basic.lean`, excluding the root aggregator `TCSlib.lean` (47 with it;
  182 `.lean` files under `TCSlib/` in total). Direct importers are 10. The
  transitive reading is the one the sentence needs — a module that reaches the
  file indirectly can still break — so the number is right, and only the word
  "importing" is ambiguous. See Advisory.
- **"fails there, at line 144, and nowhere else"** — verified, and by a stronger
  experiment than the one the report used. See below.

### "and nowhere else" — the report's reasoning does not close, but the claim is true

The report rests "nowhere else" on the green full build rather than on the
single-error log, correctly noting that the log halts at the first failure. That
is the right instinct but it does not actually close the gap: a *second* module
could also have used `List.Pairwise.forall` through `Basic.lean`, and the green
build would look identical, because the import now present supplies it to
everyone. A green build proves the fix is **sufficient**; it does not prove only
one module was **affected**.

Lake has no `--keep-going`, so I ran a two-step experiment instead:

1. Remove `import Mathlib.Data.List.Pairwise` from `Basic.lean`, full `lake build`
   → exit 1, one error:
   `LMN/NormalFormConversion.lean:144:22: Invalid field 'forall': The environment
   does not contain 'List.Pairwise.forall'`. The failure appears on removal.
2. Leaving `Basic.lean` still without it, add the import to
   `NormalFormConversion.lean` alone and rebuild → **exit 0, 3690 jobs, green.**

Step 2 is the one that settles it. If any of the other 45 modules had needed the
`Pairwise` API through `Basic.lean`, the build would still have failed with the
fix applied only at `NormalFormConversion.lean`. It did not. **`NormalFormConversion.lean`
is the only affected module — proved directly, not inferred.** Both files restored
and verified byte-identical afterwards.

### The `Real.logb` / `aesop_cat` re-attribution — conclusion right, mechanism stated too narrowly

The conclusion is **correct and now proved**: with `Mathlib.Tactic` gone from
`Basic.lean` entirely, `LMN/CircuitHelpers.lean` (`aesop_cat`) and
`LMN/IterativeReduction.lean` (`Real.logb`) both build. They were never
`Basic.lean`'s dependents in the sense round 1 assumed; they reach Mathlib through
`DecisionTree.lean`. My round-1 report repeated that misattribution from the
comment and it is corrected here.

The *explanation* offered for why round 1 missed it holds for one of the two files
only. `CircuitHelpers` does transitively import `NormalFormConversion`, so it was
genuinely masked by that file's failure. `IterativeReduction` does **not** reach
`NormalFormConversion` (nor does `BernoulliCost`) — those were masked by the
cruder fact that `lake build` aborts the entire build at the first failing module.
Same outcome, different cause. Recorded because the record should be exact; no
defect in the code.

`DecisionTree.lean` is byte-identical to my round-1 copy: its exception is
unchanged, and with `Basic.lean`'s copy deleted the comment is now duplicated
nowhere. Its own trim failure (`BernoulliCost.lean:176`, `Real.rpow_natCast`) I
verified in round 1 and it stands.

### Advisory item — `Language.unary_inPPoly` moved, and the move is axiom-neutral

`UnaryLanguages.lean:224`, immediately after `inPPoly_of_le_allOnes` (:219), in
the file's fully-qualified `Language.`-prefix style, and listed in `## Main results`
(:26) paired with `inPPoly_of_le_allOnes` under the shared [AB09, Claim 6.8] tag.
`UHalt.lean:92` still reads `unary_inPPoly _` unqualified from inside
`namespace Language` — no call site changed, and `UHalt.lean`'s `## Main results`
correctly no longer lists it.

**Axiom-neutral, verified by comparison rather than assertion.** I re-ran the full
sweep and diffed it against round 1's output: the declaration set is unchanged
(151 names, `diff` empty) and the axiom output is identical line for line once the
temp filename is normalised. `Language.unary_inPPoly` and `Language.uhalt_inPPoly`
are both `[propext, Classical.choice, Quot.sound]`, as before. `sorryAx` count 0.

### Independent re-measurement

- `lake build TCSlib.Complexity.CircuitComplexity` → exit 0, **3033 jobs**. ✓
- `lake build` (full) → exit 0, **3690 jobs**, zero errors. ✓ No warning anywhere
  in the nine files; all 27 warnings are pre-existing elsewhere
  (`MRRW.lean` ×8, `Hedge.lean` ×7, `ListDecoding.lean` ×3, `Depth3Switching.lean`
  ×2, `BLR/LowDegree.lean` ×2, and five singletons).
- `zsh scripts/lean_check.sh` on the four touched files (`Basic`, `SizeClasses`,
  `UnaryLanguages`, `UHalt`) → exit 0, **0 errors, 0 warnings** each. ✓
- Axiom sweep: **137 declarations** resolved (the report again says 51; it is still
  undercounting its own coverage), **0 `sorryAx`**, output identical to round 1.
  The 14 unresolved are the same 7 `private` declarations, 5 nested-namespace names
  and 2 scanner artifacts as before.

`awk`, the mandated command verbatim:

```
CircuitComplexity.lean         total=56  code=8   comment=47  blank=1
CircuitComplexity/Basic.lean            total=527 code=282 comment=184 blank=61
CircuitComplexity/Formulas.lean         total=92  code=24  comment=53  blank=15
CircuitComplexity/DecisionTree.lean     total=184 code=94  comment=78  blank=12
CircuitComplexity/PPoly.lean            total=139 code=47  comment=71  blank=21
CircuitComplexity/SizeClasses.lean      total=161 code=76  comment=61  blank=24
CircuitComplexity/UnaryLanguages.lean   total=225 code=114 comment=83  blank=28
CircuitComplexity/CircuitSat.lean       total=402 code=231 comment=138 blank=33
CircuitComplexity/UHalt.lean            total=103 code=39  comment=51  blank=13
```

Every delta is accounted for: `Basic` −1 line (import block), `SizeClasses` −1
(the cut sentence), `UHalt` −4 / `UnaryLanguages` +5 (the theorem moving, with its
docstring and a `## Main results` line).

### The `UHalt.lean` ratio — the question is now moot

Under the amended item 7, `UHalt.lean` is **no longer over the ratio at all**, so
it needs no structural dispensation. Its exempt content is the `## Divergences`
block (:25-39, 15 lines) and `## References` (:40-44, 5 lines), giving adjusted
`comment=31` against `code=39`. The 2 code lines the departing theorem took are
irrelevant once the block Blocking 2 mandates stops being counted as bloat.

Recomputing all nine under the amendment, exempting `## References` and
`## Divergences`:

```
                        code  comment  exempt  adjusted
CircuitComplexity.lean     8       47       6        41   OVER
Formulas.lean             24       53      13        40   OVER
PPoly.lean                47       71      16        55   OVER
UHalt.lean                39       51      20        31   ok
Basic.lean               282      184      15       169   ok
DecisionTree.lean         94       78      13        65   ok
SizeClasses.lean          76       61      14        47   ok
UnaryLanguages.lean      114       83       4        79   ok
CircuitSat.lean          231      138      24       114   ok
```

Three files remain over, not four, and all three are structural for the reason
given in round 1: the facade is 8 import lines under a `## Contents` list that
§1 mandates, and `Formulas.lean` is twelve definitions with a docstring each.
`PPoly.lean` is the widest margin and the one to watch if it grows, but its excess
is the `## Alphabet` and `## Trap` prose that Blocking 2 and Blocking 3 respectively
turn on.

The amendment also closes my round-1 Advisory on module-docstring length:
**all nine are now under the ~40-line cap**, `PPoly.lean` at 34 (was ~45 measured
the old way) and `Basic.lean` at 32.

### Round-1 corrections, accepted and confirmed

All three of my corrections to the record were taken. I confirm the third
independently: "vacuous" appears exactly once across the nine files, at
`PPoly.lean:51` ("`IsPolySize` would hold vacuously"), which is a correct
pre-existing use about a degenerate definition and unrelated to the
`by_contra`/`revert` discussion.

### Advisory (carried, not blocking)

- [Advisory] TCSlib/Complexity/CircuitComplexity/Basic.lean:10 — "the 46 modules
  importing this file" is true only under the transitive reading (direct importers
  are 10). That is the reading the sentence needs, so the claim is correct, but one
  word would remove the ambiguity in a comment whose whole value is precision.
  → "of the 46 modules that transitively import this file".
- [Advisory] TCSlib/Complexity/CircuitComplexity.lean:22-44 — unchanged from round 1:
  the `## Contents` list still orders the children …PPoly, UnaryLanguages, UHalt,
  CircuitSat, SizeClasses while the imports at :6-13 order them …PPoly, CircuitSat,
  UnaryLanguages, UHalt, SizeClasses. `CircuitSat` is the one out of place.
- [Note, orchestrator-owned] ch6/REVIEW_CRITERIA.md:14 — item 7's note now lists four
  exempt categories but item 0's own paragraph still lists three ("References, source
  tags and proof sketches"). The two passages should agree. This is the rubric, not
  the unit.

Verdict: **PASS** — zero Blocking, two Advisory and one rubric note, none of which
hold up the unit. U6 and U7 flipped to `DONE` in `ch6/PLAN.md`, closing every unit
in the plan.

## U8 — round 1 — REVISE

Independent verification (all re-run, nothing taken from the unit's report):

- `lake build TCSlib.Complexity.CircuitComplexity` → exit 0, **3042 jobs**. `Encoding.lean`
  is now registered in the aggregator (import list line 11), so this build genuinely
  covers it; the unit's standalone build is superseded.
- `lake build` (full) → exit 0, **3696 jobs** (unit reported 3690; the delta is the newly
  registered module). The only `sorry` warnings are pre-existing and out of range:
  `BLR/LowDegree.lean:883,914` and `KKL.lean:546`. Nothing in `CircuitComplexity/` or
  `NPReductions/`.
- `zsh scripts/lean_check.sh` on `Encoding.lean` and on `SATTo3SAT.lean` → no output,
  exit 0 each. Zero errors on both.
- `#print axioms` on **all 28** public declarations of `Encoding.lean` and the **3** public
  additions to `SATTo3SAT.lean` (31, not the 20 + 3 reported — the unit's count omits
  exactly the 8 declarations flagged in Blocking 1 below). Every one is
  `[propext, Classical.choice, Quot.sound]` or weaker (`ACP.unaryBits`, `ACP.readUnary`,
  `ACP.readCircuit`, `ACP.readChildren` depend on none). **No `sorryAx` anywhere.**
- Mandated `awk`, verbatim output:
  - `Encoding.lean total=428 code=245 comment=136 blank=47` — matches the unit's claim;
    comment < code.
  - `SATTo3SAT.lean total=882 code=579 comment=244 blank=59` — matches; comment < code.
- Module docstring `Encoding.lean:10–71` = 62 lines. Exempt per rubric item 0:
  `## Divergences` 32–65 (34 lines) and `## References` 67–70 (**4** lines, not 5).
  Non-exempt remainder = **24**, not the 22 reported. Under the ~40 cap either way.
- `git diff --numstat TCSlib/Complexity/NPReductions/SATTo3SAT.lean` → `53  0` — genuinely
  additive. Read the full diff: one new `Section 6` block appended before `end SATTo3SAT`;
  nothing restated, renamed, reproved or deleted. The `\ No newline at end of file` marker
  is pre-existing (it sits on an unmodified context line).
- `CircuitSat.lean` and the rest of `CircuitComplexity/` are untracked in git, so the
  orchestrator's edits could not be diffed; they were reviewed as text against the code.

### Priority 1 — is the bound's meaning stated honestly?

**Yes.** Checked each of the four points:

- `## Main results` (`Encoding.lean:29–30`) says "outputs at most `13 * |encoding|`
  **3-clauses**". It does not say "size". Correct: `to3SAT C.2.toCNF : List (Clause …)`,
  so `.length` is the clause count.
- `≤p` occurs **3 times on 2 lines** (`Encoding.lean:34` twice, `:418` once), not the two
  reported. Substantively the claim holds: both lines are disclaimers
  ("No `≤p` claim is made or supported here", "it is not a `≤p` statement"). The count is
  wrong; the property it was asserting is not.
- `## Divergences` `Encoding.lean:34–41` states the time half is unformalized and why
  (no machine model, cost bounded nowhere), and separately that the output's **bit length**
  is unbounded because `SATTo3SAT.AuxVar (BoolCircuit.CktVar n)` is infinite. Both true:
  `CktVar.gate : Circuit n → CktVar n` (`CircuitSat.lean:95`).
- `Encoding.lean:419` — "AB gives no constant; `13` is this formalization's". Present and
  correct; verified the arithmetic below.

**Not a finding, recorded so a later round does not flip it:** the declaration docstring at
`Encoding.lean:417–418` restates the module block's `≤p` disclaimer. Rubric item 7 would
forbid that, but `policy.md` §2 ("Deviations … the docstring must say so") *mandates* a
deviation notice on a declaration that is weaker than the AB result it cites, and item 0
makes policy win. Keep it.

### Priority 2 — `size_le_length_encodeSigma`

Correct, and in the useful direction. `Circuit.size` (`Basic.lean:158–160`) is
`1` at a leaf and `1 + cs.foldr (c.size + ·) 0` at a gate — exactly the `foldr` the side
induction at `Encoding.lean:337–347` uses, so the induction is against the real definition
and not a restatement. Leaf: encoding is `2 + (idx + 1) ≥ 3` bits against size `1`. Gate:
two bits plus the children block, and the side induction pays one continue bit per child.
`size_le_length_encodeSigma` then adds the arity's `n + 1` unary bits, which only helps.

Direction check: the headline needs `size ≤ |encoding|` so that `13 * size` passes to
`13 * |encoding|`. That is what is proved. The reverse would not close the goal at all
(it would leave the bound unprovable, not vacuous), so there is no silent-vacuity trap here.

Constant audit, end to end: `length_to3SAT_le` gives `f.flatten.length + 2 * f.length`;
`toCNF_flatten_length_le` gives `7 * size`; `toCNF_length_le` (`CircuitSat.lean:398`) gives
`3 * size`; `7 + 2*3 = 13`. Tight: `tseitin_flatten_length_le` is an equality at a leaf
(`4 + 3 = 7 * 1`). `gateClauses_flatten_length` re-derived by hand from
`CircuitSat.lean:107–114`: one clause of width `cs.length + 1` plus `cs.length` clauses of
width 2 = `3 * cs.length + 1`. Correct.

### Priority 3 — `FinEncoding` over `Encodable`

`Computability.FinEncoding` is used exactly as Mathlib defines it
(`Mathlib/Computability/Encoding.lean`): the four `Encoding` fields plus `ΓFin`, with
`Γ := Bool`, which satisfies `FinEncoding`'s `Encoding.{u, 0}` universe restriction. The
first reason given (`Encoding.lean:60–62`) is sound and grounded — it is an encode/decode
pair over a finite alphabet, and `ch6/PLAN.md:107` does name `FinEncoding` as the
Turing-machine track's interface. The second reason is the problem; see Blocking 2.

### Blocking

- [Blocking] TCSlib/Complexity/CircuitComplexity/Encoding.lean:92, 109, 113, 116, 238,
  270, 272, 353 — eight declarations carry no docstring: `readUnary_unaryBits`,
  `encodeCircuit_node`, `encodeChildren_nil`, `encodeChildren_cons`,
  `decodeSigma_encodeSigma`, `circuitEncoding_encode`, `circuitEncoding_decode`,
  `size_le_length_encodeSigma`. Blocking item 6 is unqualified ("every declaration has a
  docstring"), and U1 round 1 was rejected on two such gaps. `decodeSigma_encodeSigma` and
  `size_le_length_encodeSigma` are worse than incidental: both are named in
  `## Main results`, so the file advertises them and then says nothing at the declaration.
  → add one line each; say what the thing is and stop. Same defect at
  TCSlib/Complexity/NPReductions/SATTo3SAT.lean:867 (`length_to3SATAux_le`, `private` but
  still a declaration).
- [Blocking] TCSlib/Complexity/CircuitComplexity/Encoding.lean:64–65 — "which would make a
  'polynomial in the input length' statement false rather than merely unproved" asserts a
  counterfactual the file neither proves nor can prove. It is also not entailed by the
  premise: `Encodable.encode` is injective into `ℕ`, so by counting it cannot shorten more
  than `2^k` objects below `k` bits — whether such a statement came out false is
  instance-dependent, not automatic. This is the loop's recurring defect (prose asserting
  more than the code does) in the one paragraph the task flagged as "doing real work", and
  rubric item 7's "reject on any docstring that argues a point instead of stating a fact"
  is a *content* rule, which item 0's exemption does not cover — item 0 exempts the
  `## Divergences` block from item 7's **volume limits** only.
  The honest reason is already on the line above it and is sufficient: `Encodable` encodes
  into `ℕ`, so there is no string and hence no input length to be polynomial in, and
  nothing in the interface relates a Gödel number to the circuit's size.
  → cut the "false rather than merely unproved" clause and stop at the factual half.

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/Encoding.lean:11 and :323 — the module
  title and the section header both say "output **size**", while the whole point of the
  unit is that what is bounded is the clause count and not the bit length. `## Main results`
  and the theorem docstring disambiguate immediately, so this is not blocking, but "size of
  a formula" is exactly the reading the Divergences block spends four lines disowning.
  → "clause count" in both places.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Encoding.lean:263 — `circuitEncoding` is
  consumed by nothing, in this file or anywhere in `TCSlib/`; its only mentions are the two
  `rfl` lemmas beneath it. `cktSatLang` (:277) and every bound are stated against the bare
  `encodeSigma` / `decodeSigma`. Defensible as the §6.2 interface, but see the ledger note
  below — the prose elsewhere reads as though the bundle were load-bearing.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Encoding.lean:84, 87, 92 — `unaryBits`,
  `readUnary`, `readUnary_unaryBits` are generic bit-string plumbing with no circuit
  content, sitting in the topic's root namespace `ACP`. `policy.md` §1 ("do not leak
  auxiliary definitions into the root namespace; mark internal helpers `private` or put
  them in a dedicated inner namespace") points at these three. `readCircuit` /
  `readChildren` (:128, :143) are a different case and should stay public:
  `readCircuit_encodeCircuit` is a genuinely reusable fact and `decodeSigma` is stated in
  terms of them.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Encoding.lean:362, 383, 407 —
  `gateClauses_flatten_length`, `tseitin_flatten_length_le` and `toCNF_flatten_length_le`
  are counting lemmas about `CircuitSat.lean`'s own definitions, proved here by unfolding
  them (`cases b <;> simp [gateClauses, key]`). The unit is right that this is where the
  constants 7 and 13 become hostage to that file's internal shape. It should be insulated:
  the natural home is `CircuitSat.lean`, beside `Circuit.toCNF_length_le` (:398), which is
  the same kind of lemma about the same definitions and is already there. Only
  `length_to3SAT_toCNF_le` needs the encoding and needs to be in this file. Not blocking —
  it is a relocation, the proofs are unaffected, and per the rubric's "File ownership"
  section cross-file moves belong to the cross-track pass.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Encoding.lean:277 — **namespace ruling.**
  The precedent U8 cited does not support the choice: `ACP.CircuitFamily.language`
  (`PPoly.lean:85`) is a projection-style def inside a structure's namespace, not a named
  language constant. The real comparanda are `Language.allOnes` (`SizeClasses.lean:67`),
  `Language.unary` and `Language.uhalt` (`UHalt.lean:71,89`) — three `Language Bool`
  constants in this same topic, all in namespace `Language`, and under that convention the
  `Lang` suffix on `cktSatLang` would be unnecessary. **But** `policy.md` §1 says
  "pick one namespace root per topic and use it consistently within that topic", and the
  topic's root is `ACP`; on that reading the three `Language.*` definitions are the
  deviants, not this one. Policy outranks the rubric (item 0), so this is **not blocking**
  and U8's choice is defensible. It is nonetheless an inconsistency inside one topic, and
  the rubric assigns exactly that to the orchestrator's cross-track pass. Rule it one way
  for all four and move whichever three are on the losing side.
- [Advisory] ch6/NOT_FORMALIZED.md:25 — "`ACP.cktSatLang : Language Bool` now exists via a
  `Computability.FinEncoding`" overstates the link: `cktSatLang` is defined directly from
  `decodeSigma`, and `circuitEncoding` is not in its definitional path (see above). Also,
  `CLOSED by U8` is a fourth status not in the file's own legend (lines 6–8: `JUDGMENT` /
  `BLOCKED` / `PARTIAL`). → either add `CLOSED` to the legend or use `PARTIAL`, which is
  arguably more accurate given the same row says AB's matrix form is not formalized.
  The rest of the row, and rows 23 and 43, were checked against the code and are accurate:
  `mem_cktSat_iff_is3Satisfiable` (`CircuitSat.lean:356`) and `length_to3SAT_toCNF_le`
  exist and say what the row says; `CktVar` is infinite for the stated reason; the
  re-indexing fix named is the right one.
- [Advisory] ch6/PLAN.md:169 — "AB specifies the encoding itself… Following AB's own spec
  also makes this the piece §6.2 will need" is no longer true of the delivered unit, which
  deliberately did not follow AB's spec. The divergence is properly recorded in
  `Encoding.lean:43–50` and in `NOT_FORMALIZED.md:43–49`, so nothing is concealed, but the
  plan text now contradicts both. Orchestrator-owned; update it when U8 lands.

### Checked and clean

- **Re-encode guard is not circular.** `decodeSigma` (:230) checks `encodeSigma ⟨n,C⟩ = bs`,
  and `decodeSigma_encodeSigma` (:238) discharges that check using
  `readCircuit_encodeCircuit` (:200), which is proved by structural induction on the circuit
  with no reference to `decodeSigma`. The `mutual` parser and
  `readChildren_encodeChildren` (:168) likewise stand alone. `encodeSigma_of_decodeSigma`
  (:247) then reads the guard straight back out, which is what makes
  `mem_cktSatLang_iff_exists` (:291) an iff rather than one inclusion. Fuel is sound:
  `decodeSigma` passes `r.length`, and on a canonical string `r` *is* `encodeCircuit C`.
- **Unary naturals.** Traced every use. `unaryBits` lengths appear only on the right-hand
  (larger) side of an inequality — `size_le_length_encodeCircuit` at the leaf,
  `size_le_length_encodeSigma` for the arity, `length_to3SAT_toCNF_le` for the final bound
  — and as the *fuel* argument in `decodeSigma`, where more is also safe. There is no
  statement in the file with an encoding length on the small side, so the "harmless
  direction" claim (:53–55) holds everywhere it is used. Worth noting for the record that
  the inflation is polynomial (a leaf index costs `O(n)` bits rather than `O(log n)`), which
  is what makes it harmless for a future `≤p`-style claim rather than merely convenient here.
- **Blocking 3, degenerate cases.** `Encoding.lean:302–321` exercises zero inputs, the empty
  `AND`, the empty `OR`, a single literal, and the empty string. `cktSatLang` is neither
  empty nor everything, and `[] ∉ cktSatLang`. Not vacuous.
- **AB fidelity.** The adjacency-matrix form and the `SIZE`/`TYPE`/`EDGE` accessors are not
  implemented, and `Encoding.lean:43–50` says so explicitly, gives the reason
  (`BoolCircuit.Circuit` is a tree with no vertex identities), and states what this file does
  instead. Nothing in the file implies it follows AB's representation. Recorded in the ledger
  at `NOT_FORMALIZED.md:25` and :43–49 as well. Clean.
- **Orchestrator's `CircuitSat.lean` edits.** Both replaced sentences now match the code.
  "AB's CKT-SAT is a language of *strings representing* circuits, whereas `CktSat` is a set
  of circuits… `CircuitComplexity.Encoding` supplies one downstream, and with it a clause
  count bounded in the encoded input length — still not a `≤p` claim" is accurate on every
  clause, including the "clause count" wording that `Encoding.lean`'s own title does not use.
  The forward reference creates no import cycle (`Encoding` imports `CircuitSat`, not the
  reverse). `CircuitSat.lean:30–31`, "Only equisatisfiability is formalized, not `≤p`:
  TCSlib has no machine model, and this file proves no bound on the reduction's cost", is
  **still correct for that file**: the only quantitative result it proves is
  `toCNF_length_le`, a clause count, and "cost" reads as time, which the following sentences
  make explicit. The file builds (covered by both green builds above).

Verdict: **REVISE** — two Blocking. The bound's meaning *is* stated honestly and the
mathematics is sound end to end; both Blocking items are prose, and both are small edits.

## U8 — round 2 — PASS

Both round-1 Blocking items are fixed, and the three accepted Advisories are applied.
Everything below was re-run from scratch; nothing was taken from the unit's report.

### Round-1 Blocking items — both resolved, drop

- **Blocking 1 (nine missing docstrings) — fixed.** Verified with my own sweep, not the
  unit's. The sweep walks back over `@[...]` attribute lines, accepts the `private` /
  `protected` / `noncomputable` / `partial` modifiers, and **prints the number of
  declarations it found** alongside the number missing, so an empty result cannot be
  confused with a sweep pointed at the wrong thing:

  ```
  Encoding.lean:   declarations found=28  missing docstring=0
  SATTo3SAT.lean:  declarations found=41  missing docstring=0
  ```

  Three independent confirmations that the sweep is looking in the right place: (i) a
  canary file with one documented and one undocumented theorem reports `found=2 missing=1`
  and names the right line; (ii) `found=28` for `Encoding.lean` reproduces exactly the
  round-1 hand enumeration of that file's declarations; (iii) `41 − 37 = 4` against
  `git show HEAD:…SATTo3SAT.lean`, matching the four theorems U8 added.
  Read all nine new docstrings: one line each (two for `length_to3SATAux_le`, within item
  7's "one or two lines"), each stating what the thing is, none restating a module-block
  decision.
- **Blocking 2 (the `Encodable` over-reach) — fixed.** `Encoding.lean:64–66` now reads
  "`Encodable`/`Denumerable` were not used because they encode into `ℕ`, which supplies no
  string and so no input length for a bound to be stated in." The counterfactual and the
  "exponentially shorter" premise are both gone, and what remains is the grounded reason.
  Swept the whole file for surviving counterfactuals (`would`/`could`/`exponential`/
  `false`/`rather than merely`): the only hits are `Encoding.lean:56–57`, the unary
  paragraph, which is accurate and which round 1 itself proposed. Clean.

### Advisories — applied

- Title (`:11`) and section header (`:332`) now say "clause count"; `grep` finds no
  "output size" anywhere in the file. `≤p` is unchanged at 3 occurrences on 2 lines
  (`:34` twice, `:428`), both disclaimers, as accepted in round 1.
- The unary paragraph (`:53–57`) now states the inflation as fact and quantifies it:
  `O(n)` rather than `O(log n)` bits for an index below `n`, "and only upwards". Both
  clauses check out against `unaryBits` and against every use traced in round 1.
- `unaryBits`, `readUnary`, `readUnary_unaryBits` are `private` (`:85, :88, :94`);
  `readCircuit` (`:134`) and `readChildren` (`:149`) stay public, as recommended.

### The private-in-public-statement check

**The unit's stated premise for this check is wrong, and the coordinator repeated it: a
private in a public statement would *not* be a build-visible error.** Lean 4 privates are
module-scoped — a public theorem whose type mentions one still elaborates, in this module
and downstream, because the constant exists and only its *name* is unavailable. So both
green builds prove nothing here. I checked it directly instead, from a separate file that
imports the module: `#check` on all 24 public declarations of `Encoding.lean` produces no
`_private` in any signature and no error. Confirmed the privates are genuine (not
decorative) by the converse test — `#check @ACP.unaryBits` from downstream fails with
`Unknown identifier`. The claim is true; the reasoning offered for it was not.

Residual, not a finding: `encodeCircuit`, `encodeSigma` and `readCircuit` are public defs
whose *bodies* call the now-private helpers, so a downstream `simp [encodeCircuit]` can
surface an unnameable `_private…` constant. `encodeCircuit_node`, `encodeChildren_nil` and
`encodeChildren_cons` are the public rewrite interface that makes this a non-issue in
practice, and nothing downstream exists yet to be inconvenienced.

### Adjudication: 31 vs 32 — the unit is right, and so was round 1

Both numbers are correct for their stated scope, and the scope changed between rounds.

- Round 1 counted **public** declarations: 28 in `Encoding.lean` (all of them were public
  then) + 3 public additions to `SATTo3SAT.lean` = **31**, with `length_to3SATAux_le`
  excluded as private. That was stated as "public declarations" and was right.
- Round 2 made three `Encoding.lean` helpers private, so the file is now 25 public + 3
  private. Counting **every** declaration gives 28 + 4 = **32**. Also right, and the better
  convention going forward — it is scope-stable, whereas a public-only count silently
  changes whenever a helper is marked private, which is exactly what happened here.

Reproduced **32** independently, and the method matters: the four privates are **not
nameable from an importing file**, so this sweep cannot be run downstream —
`#print axioms ACP.unaryBits` there fails with `Unknown constant`. It has to be run
in-module. Re-ran it that way, appending the prints inside each file's namespace:

```
Encoding.lean   prints=28  sorryAx=0  errors=0
SATTo3SAT.lean  prints=4   sorryAx=0  errors=0
```

All 32 are `[propext, Classical.choice, Quot.sound]` or weaker; the privates appear as
`_private._stdin.0.…`. **No `sorryAx`.** Worth recording that my first attempt at this
sweep silently produced an *empty* input file (`head -n -1` is a GNU-ism; BSD `head` on
this machine rejects it), and the instrumentation caught it — `prints=0`. That is the
failure mode the coordinator asked about, and it is why every sweep in this entry reports
what it found and not only what it failed to find.

Soundness note: 32 is more thorough but not more conclusive than 31. `sorryAx` propagates
through dependencies, and every private here is reachable from a public — `unaryBits` from
`encodeCircuit`, `readUnary` from `readCircuit`, `readUnary_unaryBits` from
`readCircuit_encodeCircuit`, `length_to3SATAux_le` from `length_to3SAT_le`. A clean public
sweep already ruled out a `sorry` hiding in a private.

### Measurements

All four of the unit's figures reproduce exactly.

- `awk` (mandated command), verbatim:
  - `Encoding.lean total=438 code=245 comment=146 blank=47`
  - `SATTo3SAT.lean total=884 code=579 comment=246 blank=59`
  Comment < code in both. `code` is unchanged from round 1 at 245 and 579, confirming the
  round consisted of prose plus three `private` modifiers and touched no proof.
- `lake build TCSlib.Complexity.CircuitComplexity` → exit 0, **3042 jobs**.
- `lake build` → exit 0, **3696 jobs**.
- `zsh scripts/lean_check.sh` → no output, exit 0, on both files.
- `git diff --numstat …/SATTo3SAT.lean` → `55  0`. Still additive; the +2 over round 1 is
  the two-line docstring on `length_to3SATAux_le`.
- Module docstring `:10–72` = 63 lines; exempt `## Divergences` `:32–66` (35) and
  `## References` `:68–71` (4); non-exempt remainder **24**, under the ~40 cap.

Correction to my own round-1 entry: the pre-existing `sorry` list I gave was incomplete. A
fully cold full build reports them in `ErrorCorrectingCodes/MRRW.lean` (7),
`BooleanAnalysis/LMN/` (`CircuitCompression`, `IterativeReduction`, `Depth3Switching` ×2,
`CircuitTreeManip`), `BLR/LowDegree.lean` (2) and `KKL.lean` — round 1 saw only the tail
because the rest were replayed from cache. All are pre-existing and out of range; nothing
in `CircuitComplexity/` or `NPReductions/`. The conclusion is unaffected.

### Coordinator's own files — both fixes verified

- `ch6/NOT_FORMALIZED.md:25` — status is back to `PARTIAL`, which is in the legend at
  lines 6–8. The row now says `cktSatLang` is "defined directly from `ACP.decodeSigma`"
  and that `circuitEncoding` "is not in `cktSatLang`'s definitional path and currently has
  no consumer". Both independently confirmed: `cktSatLang` (`:286`) is `decodeSigma`-based,
  and `grep` for `circuitEncoding` outside `Encoding.lean` returns nothing.
- `ch6/PLAN.md` U8 — the stale "Following AB's own spec…" is gone, replaced by an accurate
  statement that the matrix form needs vertex identities the tree does not have, that U8
  serialised structurally, and that §6.2 will still need AB's form. Matches
  `Encoding.lean:43–50` and `NOT_FORMALIZED.md:43–49`.

### Advisory (new, minor; none hold up the unit)

- [Advisory] TCSlib/Complexity/CircuitComplexity/Encoding.lean:429 — "read off the clause
  counts **below**" points the wrong way: `toCNF_flatten_length_le` (`:416`),
  `tseitin_flatten_length_le` and `gateClauses_flatten_length` are all *above* this
  declaration. Present in round 1 and missed then. One word.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Encoding.lean:427 — "This is the **size**
  half of the lemma" is the one "size" left in the file now that the title and section
  header say "clause count". It is not misleading — the next clause defines it, and
  "size half vs time half" is the plan's own dichotomy — but it is now internally
  inconsistent with the file's own heading.
- [Advisory] ch6/PLAN.md:152, 163, 174 — "the size half of Lemma 6.11", "the reduction's
  output size", "delivers a polynomial *size* bound". Same wording the Lean file was moved
  off for the same reason; the plan is what a later unit reads. Orchestrator-owned.

### Standing, deferred by instruction — not re-raised

Relocating `gateClauses_flatten_length` / `tseitin_flatten_length_le` /
`toCNF_flatten_length_le` into `CircuitSat.lean`, and the `ACP`-vs-`Language` placement of
`cktSatLang`, remain open for the cross-track pass. The unit withdrew the
`ACP.CircuitFamily.language` precedent rather than restating it, which is the right call —
that argument was wrong, and `policy.md` §1's "one namespace root per topic" is the reading
that makes `ACP.cktSatLang` defensible.

The unit's own note that its round-1 report to the coordinator repeated the over-reach
("a substantive ground, not taste") is accurate and is the correct diagnosis: the ground
was real, the sentence built on it was not. That is the same defect the log has been
tracking, appearing in a report rather than in a docstring.

Verdict: **PASS** — zero Blocking. Three minor Advisories, none of which hold up the unit.
The bound's meaning is stated honestly, the mathematics was verified sound in round 1 and
is untouched (`code` unchanged in both files), and all 32 declarations are `sorry`-free.
U8 flipped to `DONE` in `ch6/PLAN.md`.

---

## U9 — round 1 — REVISE

File under review: `TCSlib/Complexity/CircuitComplexity/Universal.lean` (167 lines).

### Independent measurements (all re-run, not taken from the unit's report)

- `lake build TCSlib.Complexity.CircuitComplexity.Universal` — **916 jobs, exit 0**. Matches.
- `lake build TCSlib.Complexity.CircuitComplexity` (aggregator, now that the module is
  registered) — **3043 jobs, exit 0**. Matches.
- `lake build` (full) — **3697 jobs, exit 0**. The unit reported 3696; the run here is
  after the aggregator registration, so +1 is expected. Only warning in the whole build is
  a pre-existing unused-variable linter hit at `TCSlib/LearningTheory/Hedge.lean:374`.
- `zsh scripts/lean_check.sh TCSlib/Complexity/CircuitComplexity/Universal.lean` — **no
  output, clean**.
- `#print axioms` on all **11 public** declarations: every one is
  `[propext, Classical.choice, Quot.sound]` except `ACP.minterm`, which depends on none.
  **No `sorryAx`.** `grep sorry` on the file returns nothing. The **2 private** helpers
  (`lit_eval_iff:71`, `foldr_size_map:76`) are consumed by the public ones, so they are
  covered transitively. 13 declarations total — matches the report.
- Mandated `awk`, verbatim output:

  ```
  total=167 code=76 comment=71 blank=20
  ```

  Matches the unit's figure exactly. Comment (71) is under code (76).
- Module docstring is lines 10–58 = **49 lines**. See Advisory A1 on the exemption split.
- **The `lakefile.lean` point is confirmed.** `lakefile.lean` declares a bare
  `lean_lib «TCSlib»` with no `globs`, so Lake's default target is `TCSlib.lean` and its
  transitive imports only — a module in the directory but not imported is not in the
  default build at all. U9's claim that its file "is currently built only because lake
  globs the directory" was **false**; it built because U9 named the module explicitly.
  Independent evidence in the same directory: `HardFunctions.lean` and `NCAC.lean` exist
  on disk and are *not* in the aggregator, and the full build is 3697 jobs — it does not
  reach them.

### Degenerate cases — verified in Lean, not by reading

Compiled against the real module (`lake env lean`, zero errors):

- `n = 0`, `f ≡ true`: `(universalCircuit _).size = 2` — via `universalCircuit_const_true_size`
  plus `norm_num`. Confirmed.
- `n = 0`, `f ≡ false`: `(universalCircuit _).size = 1`, **and** the circuit *is*
  `.node false []` — `universalCircuit_const_false` closes the second goal by `exact`,
  so the identity is definitional-strength, not merely an eval agreement. Confirmed.
- `minterm` at `n = 0` has size 1 (the empty conjunction). Confirmed.
- **The bound is genuinely attained, for every `n`.** `universalCircuit_const_true_size`
  (`:158`) is an *equation* `... .size = 2 ^ n * (n + 1) + 1` universally quantified over
  `n`, not an instance. Spot-checked at `n = 3` (`= 8 * 4 + 1`). The docstring's "a bound
  `ACP.universalCircuit_const_true_size` shows is attained" (`:28–29`) is accurate: the
  constant cannot be lowered for this construction.

### `noncomputable` — ruling: the call is correct, no change

Verified mechanically rather than argued. `Finset.univ.filter (fun v => f v = true)`
compiles as a plain `def` (checked: `testA` elaborates with no `noncomputable`), and adding
`.toList` produces

```
failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'Finset.toList', which is 'noncomputable'
```

So the docstring's "`universalCircuit` is `noncomputable` only because `Finset.toList` is"
(`:51–52`) is verified verbatim by the compiler, and `Finset.filter`'s decidability is not
at issue. Both cited precedents are real and in the same directory:
`UnaryLanguages.lean:149` (`noncomputable def unaryFamily`) and `DecisionTree.lean:179`
(`noncomputable def dtDepth`). Nothing downstream needs to *run* this circuit —
`exists_circuit_eval_eq_size_le` is `Prop`-valued — so the ~30 lines of hand-rolled
`allAssign` + `Nodup` would buy nothing and would be new code where existing code serves,
against policy §1. **Not overturned.**

### Reuse decision — ruling: sound, and every claim in the file checks out

Policy §1 Blocking-4 question, resolved in the unit's favour. The file (`:48–52`) gives
**three** reasons; all three are mechanically true:

1. `DNF` is built on `Literal` (`Formulas.lean:50`), a type distinct from `Basic.lean:80`'s
   `Lit` — different field names (`var`/`neg` vs `idx`/`sign`) and *opposite polarity
   convention* (`Literal.neg = true` means negated; `Lit.sign = true` means positive).
   Confirmed.
2. `Formulas.lean` defines no size measure on `DNF` — only `DNF.width` (`:73`). Confirmed,
   and `Formulas.lean`'s own docstring (`:31–32`) says so: "[OD14, Def 4.3] also gives a
   formula a *size*, its number of terms; no size measure is defined here."
3. No `DNF → Circuit` map anywhere in `TCSlib/`. Confirmed by grep over all 24 files that
   mention `DNF`. The two bridges run the other way and are at exactly the cited lines:
   `NOrCircuit.toDNF` at `LMN/NormalFormConversion.lean:54` and `depth2OrToDNF` at
   `LMN/CircuitHelpers.lean:309`. Both confirmed.

See Advisory A2 for the fourth reason, which is not in the file.

### Divergence 1 (CNF/DNF duality) — verified accurate

Against AB p. 46 (PDF 72). AB's proof of Claim 2.13 reads: "We let ϕ be the AND of all the
clauses C_v for v such that f(v) = 0", i.e. `ϕ = ⋀_{v : f(v)=0} C_v`. The docstring's
`⋀_{v : f v = 0} C_v` over *falsifying* assignments (`:34`) is exact, and the dual
`⋁_{v : f v = 1} T_v` (`:35`) is what `universalCircuit` (`:111–112`) builds. "Both are one
gate over at most `2ⁿ` gates of `n` literals" (`:35–36`) is also right on both sides: AB's
`C_v` is a clause in exactly ℓ variables (his worked example `v = 1,1,0,1` gives a 4-literal
clause), and `minterm` is an `AND` of exactly `n` literals (`minterm_size:104`, `= n + 1`
nodes). The divergence is deliberate, class-preserving and recorded. No finding.

### Docstring-vs-code fidelity — clean, including the two the brief singled out

Checked all 13 declaration docstrings against their statements plus the header.

- `:19` "the `AND` of `n` literals that is true exactly at `v`" — exact. `minterm` is
  `.node true` over `(List.finRange n).map`, so exactly `n` literals; `minterm_eval_iff:89`
  is `(minterm v).eval x = true ↔ x = v`, which is "exactly at `v`", not "at least at `v`".
  Holds at `n = 0` too, where `Fin 0 → Bool` is a singleton. Accurate.
- `:36` "Both are one gate over at most `2ⁿ` gates of `n` literals" — accurate, see above.
- `:26–27` "exactly `(n + 1)` times the number of satisfying assignments, plus one" —
  `universalCircuit_size:130` is `card * (n + 1) + 1`. Exact, and "exactly" is earned: it is
  an equation, not a bound.
- `:152` `universalCircuit_const_false` — "No satisfying assignment: the circuit is the
  empty `OR`." No size claim. The trim the unit reported making was made, and the remaining
  sentence is exactly what the equation says.
- `:144–145` "[AB09, Claim 2.13], as cited at [AB09, p.108]" — verified. AB p. 108 (PDF 134):
  "Since a CNF formula is a special type of a circuit, Claim 2.13 shows that every function
  f from {0,1}ⁿ to {0,1} can be computed by a Boolean circuit size n2ⁿ."
- `:45–46` "[AB09, Ex 6.1]'s sharper `O(2ⁿ/n)`" — verified, same paragraph on p. 108.

No fidelity defect in any declaration docstring. The standing failure mode is, this round,
confined to the module block — see Blocking B1 — and to the two ledger files.

### Blocking

- [Blocking] `TCSlib/Complexity/CircuitComplexity/Universal.lean:39–46` — **the account of
  the constant is assembled from true facts but is not a correct explanation: it
  misrepresents AB, and it does not predict the number it is offered to explain.**

  What is right, and verified against the PDF rather than assumed:
  - AB p. 46 (PDF 72), Claim 2.13, states the convention inside the claim itself: "...there
    is an ℓ-variable CNF formula ϕ of size ℓ2^ℓ ... *where the size of a CNF formula is
    defined to be the number of ∧/∨ symbols it contains*." So "`n2ⁿ` is Claim 2.13's count
    of ∧/∨ symbols" is correct.
  - AB p. 107 (PDF 133), Def 6.1: "a directed acyclic graph with n sources ... The vertices
    labeled with ∨ and ∧ have fan-in ... equal to 2 ... **The size of C, denoted by |C|, is
    the number of vertices in it.**" So "Def 6.1 sizes a circuit by its vertex count on a
    fan-in-2 DAG whose `n` sources are shared" is correct.
  - `Basic.lean:157–159`: `Circuit.size` is `1 + Σ children` with `.lit _ => 1`, on a tree.
    So "counts every node ... literal leaves included, and a variable read `k` times
    contributes `k` leaves" is correct.

  What is wrong is the inference built on them, in two ways.

  **(i) The contrast drawn at `:39–41` does not exist in AB.** The sentence sets AB's `n2ⁿ`
  (a symbol count) against Def 6.1 (a vertex count), implying `n2ⁿ` is an artifact of the
  Chapter-2 convention that Def 6.1 would not give. It is not: `n2ⁿ` is correct under *both*,
  and p. 108 asserts it as a Def-6.1 *circuit* size, not as a formula size. Counting AB's own
  object under Def 6.1 — `n` shared sources, `n` shared `¬` gates, each ℓ-literal clause as
  `n−1` fan-in-2 `∨` gates, the top `∧` as `2ⁿ−1` gates — gives `n·2ⁿ + 2n − 1` vertices.
  The divergence is therefore **not** between AB's two conventions; it is between AB's
  DAG-with-sharing and our tree. As written, the docstring tells a reader of U11 that AB's
  figure is convention-bound when it is not.

  **(ii) The reasons given predict the wrong magnitude.** Every mechanism named at `:41–43`
  pushes the count *up* (all nodes counted, leaves counted, `k` reads = `k` leaves, tree not
  DAG). Taken alone they predict roughly `2n·2ⁿ`. The number actually proved is
  `n·2ⁿ + 2ⁿ + 1`. What pins it there is the *offsetting* effect the docstring never
  mentions: `Circuit.size` charges **1** for an unbounded-fan-in gate where AB charges `k−1`
  symbols (or `k−1` fan-in-2 gates), saving `(n−1)2ⁿ + 2ⁿ − 1` here. The "therefore" at `:43`
  is not earned.

  The exact accounting, for the full (all-`2ⁿ`) case:

  | measure | value |
  |---|---|
  | AB Claim 2.13, ∧/∨ symbols | `(n−1)2ⁿ + (2ⁿ−1) = n·2ⁿ − 1` |
  | AB Def 6.1, vertices (shared sources and `¬`) | `n·2ⁿ + 2n − 1` |
  | `Circuit.size` (this file) | `n·2ⁿ` leaves + `2ⁿ` minterm gates + `1` top gate = `2ⁿ(n+1) + 1` |

  So our excess over AB's symbol count is exactly `2ⁿ + 2`. Note what that table shows: our
  leaf count `n·2ⁿ` **numerically coincides** with AB's symbol count. The leaves are not the
  source of the excess — the *gate nodes* are, and the symbol convention does not charge them
  at all.

  → Replace `:39–46` with that accounting, in two sentences: AB's `n2ⁿ` is Claim 2.13's
  ∧/∨-symbol count and, to lower order, Def 6.1's vertex count for the same formula, because
  sources and `¬` gates are shared and a `k`-ary gate costs `k−1` fan-in-2 gates;
  `Circuit.size` counts tree nodes, whose `n·2ⁿ` literal leaves happen to match AB's symbol
  count, plus the `2ⁿ+1` gates the symbol convention does not charge — hence `2ⁿ(n+1)+1`,
  the same order, larger by `2ⁿ+2`. Keep `:44–46` (`O(2ⁿ/n)` not attempted) as is.

  **Ruling on the question the brief asks:** not a plausible story attached to a number that
  came out of the construction — every cited fact about AB is real and checks out on the
  page. But not a correct explanation either: it is a half-account that omits the effect
  doing the arithmetic work and manufactures a disagreement inside AB. This must be fixed
  before U11 consumes the bound, since U11's whole framing is "our constant, not AB's".

- [Blocking] `ch6/PLAN.md:101` — the **explicit skip list** still carries
  "| Claim 2.13 / Exercise 6.1 size bounds (`n2ⁿ`, `O(2ⁿ/n)`) | Cited from Chapter 2, not
  proved on these pages. |", under a heading that reads "**do not formalize**; recorded so
  the loop does not revisit". Ten lines below, `:111` has "U9 — Claim 2.13 ... WIP", and
  `:143` has U11 consuming it. The orchestrator split the corresponding row in
  `NOT_FORMALIZED.md:27–28` but left `PLAN.md`'s own copy untouched, so the plan now
  instructs the loop both to skip and to formalize the same claim. This is the exact defect
  the skip list exists to prevent. → Split it the same way: drop Claim 2.13 (it is U9), keep
  Exercise 6.1's `O(2ⁿ/n)`.

- [Blocking] `ch6/NOT_FORMALIZED.md:27` — "**AB's figure counts ∧/∨ symbols on a fan-in-2
  DAG with shared sources**" is false about the book. Claim 2.13 is on p. 46, in Chapter 2,
  four chapters before circuits are defined; it is a statement about a CNF **formula** and
  mentions no graph, no fan-in and no sources. "fan-in-2 DAG with shared sources" is
  Def 6.1's separate, *vertex*-based convention on p. 107. The row has fused the two
  conventions that `Universal.lean:39–41` keeps distinct into a single convention that
  exists in neither place — so the orchestrator's row is strictly worse than the docstring it
  was summarising. → Either state the two separately, or drop the mechanism from the row and
  keep only "our constant `2 ^ n * (n + 1) + 1`, not AB's `n2ⁿ`; same order, different
  number", leaving the explanation to the docstring.

### Advisory

- [Advisory] `TCSlib/Complexity/CircuitComplexity/Universal.lean:48–52` — this paragraph is
  a **reuse/design decision, not a divergence from AB**, but it sits inside the
  `## Divergences from [AB09, Claim 2.13]` block. Item 0 exempts that block because item 2
  *mandates* it; the exemption does not reach design rationale parked under the same
  heading. The unit's reported split ("Divergences (21) and References (4) ... leaving 24")
  therefore over-claims the exemption by the 5 lines `:48–52`. The honest split is: docstring
  49 lines; exempt = AB divergences `:32–46` (15) + References `:54–57` (4) = 19;
  non-exempt = **30**. Still comfortably under the ~40 cap, so this changes no verdict —
  but the figure quoted was not the figure measured, and item 7 is explicit that counts must
  reproduce. → Give `:48–52` its own `## Design notes` heading and count it against the cap,
  where it fits.

- [Advisory] `TCSlib/Complexity/CircuitComplexity/Universal.lean:48–51` — the file gives
  **three** reasons for not reusing `DNF`, all verified above. A **fourth** was attributed to
  this unit in the review brief — "both live under `BooleanAnalysis`, which `Complexity`
  should not import" — and it is **not in the file**. Just as well: it would be false.
  `TCSlib/Complexity/CircuitComplexity/PPoly.lean:7` already imports
  `TCSlib.BooleanAnalysis.RazborovSmolensky.ACpGates`, and every `LMN/*` file imports
  `TCSlib.Complexity.CircuitComplexity.Basic`, so `Universal → LMN/NormalFormConversion`
  would be acyclic and permitted. The genuine objection is layering weight — a four-line
  Chapter-6 file should not drag in the switching-lemma development — and that is worth one
  clause if the paragraph is kept. Relatedly, the `Literal ↔ Lit` distinction the brief says
  U9 draws is **not drawn anywhere in the file**; nothing needs adding, but note that
  `BoolCircuit.Lit.toLiteral` lives at `LMN/NormalFormConversion.lean:29`, not
  `LMN/CircuitHelpers.lean`. The file's actual sentence — "`Literal`, a type distinct from
  `Basic.lean`'s `Lit`" — claims only distinctness and is true.

- [Advisory] `ch6/NOT_FORMALIZED.md:27` vs `:7` — the legend defines `PARTIAL` as "some of
  it is formalized, **and the entry says which part is not**". The row says the claim is
  proved outright, with a different constant; it never names an unformalized part. If the
  intended unformalized part is "AB's `n2ⁿ` as such", say that in those words, otherwise the
  row does not satisfy its own legend. (Also `:4` scopes the ledger to "AB pp. 108–113
  (PDF 134–139)", and this row's primary source is p. 46 / PDF 72.)

### The orchestrator's other edits — checked, and these are clean

- `TCSlib/Complexity/CircuitComplexity.lean:12` (import) and `:48–50` (`## Contents` bullet)
  — registered correctly, and the bullet's text ("every Boolean function on `n` bits is
  computed by a circuit of size at most `2 ^ n * (n + 1) + 1`, via the DNF over its
  satisfying assignments") matches `exists_circuit_eval_eq_size_le:146–148` exactly, constant
  included. Confirmed by the 3043-job aggregator build.
- `ch6/PLAN.md:111` — U9 flipped to `WIP`. Correct.
- `ch6/PLAN.md:143–146` — the U11 note. Accurate: the bound is `2 ^ n * (n + 1) + 1`, the
  hook `ACP.exists_circuit_eval_eq_size_le` exists under that exact name and states exactly
  that. Good that it was added; U11 would otherwise have written AB's number.
- `ch6/NOT_FORMALIZED.md:28` — the Exercise 6.1 row, left as `JUDGMENT`. Correct: p. 108
  confirms Exercise 6.1 is a separate and sharper construction, and `Universal.lean:45–46`
  says it is not attempted.

### Verdict

**REVISE** — three Blocking. The mathematics is sound and I found no false theorem: all 11
public declarations are `sorry`-free with clean axiom sets, the bound is exact and attained,
the degenerate cases behave as claimed, the CNF/DNF duality is faithful to p. 46, and the
reuse and `noncomputable` calls are both correct and both survive review. Every finding is
again prose — the module block's account of the constant (B1), and the two orchestrator
ledger rows (B2, B3), one of which is a false statement about the book. Fifteen rounds,
same failure mode, still never a false theorem.

`ch6/PLAN.md` U9 left at `WIP`.

---

## U10 — round 1 — REVISE

File under review: `TCSlib/Complexity/CircuitComplexity/HardFunctions.lean` (266 lines).
Dependency read in full: `CircuitComplexity/Encoding.lean` (439 lines).

### Measurements — every figure independently reproduced

| claim | reproduced | result |
|---|---|---|
| module build | `lake build TCSlib.Complexity.CircuitComplexity.HardFunctions` | **1030 jobs, success**, no errors or warnings |
| aggregator (module now registered) | `lake build TCSlib.Complexity.CircuitComplexity` | **3044 jobs, success** — matches |
| full build `3697 jobs` | `lake build` | **3698 jobs, success** — see A8 |
| `lean_check.sh` zero diagnostics, exit 0 | `zsh scripts/lean_check.sh …/HardFunctions.lean` | **zero output, exit 0** ✓ |
| five public decls, all `[propext, Classical.choice, Quot.sound]` | `#print axioms` on each | ✓ all five, **no `sorryAx`** |
| `awk` counts | rubric item 7's mandated command | `total=266 code=140 comment=105 blank=21` ✓ comment < code |
| docstring 52 lines, Divergences 29 + References 4, leaving 19 | lines 11–62 = 52; `## Divergences` 29–57 = 29; `## References` 58–61 = 4 | ✓ **19 non-exempt**, well under ~40 |

Declaration inventory: exactly 5 public theorems (`:135, :163, :182, :215, :241`), 5
`private` (`:76, :80, :90, :95, :114`), 2 `example`s. No `sorry`, no `admit`, no
`native_decide`. Every declaration carries a docstring. No minimality is asserted
anywhere — `grep -niE "tight|optimal|minimal|sharp|cannot be improved"` returns nothing,
and every bound in the file is `≤` or `<`.

### Blocking

- [Blocking] `TCSlib/Complexity/CircuitComplexity/HardFunctions.lean:37–39` — **"and is a
  correspondingly weaker conclusion at any `S`" is false, and contradicts line 31 of the
  same paragraph.**

  What is right, checked against the PDF rather than assumed:
  - AB p. 107 (PDF 133), Def 6.1: "a directed acyclic graph with `n` sources (vertices with
    no incoming edges) and one sink … The vertices labeled with ∨ and ∧ have fan-in … equal
    to 2 and the vertices labeled with ¬ have fan-in 1. **The size of `C`, denoted by `|C|`,
    is the number of vertices in it.**" So the docstring's "DAG whose ∨/∧ gates have fan-in
    2 and whose ¬ gates have fan-in 1, with size its number of vertices — one source vertex
    per input variable, however often that variable is read" is **correct in every clause**.
  - AB p. 115 (PDF 141), Thm 6.21: "For every `n > 1`, there exists a function
    `f : {0,1}ⁿ → {0,1}` that cannot be computed by a circuit `C` of size `2ⁿ/(10n)`",
    proved by "every circuit of size at most `S` can be represented as a string of
    `9 · S log S` bits (e.g., using the **adjacency list** representation)". The docstring
    cites `9 · S · log S` and "adjacency list" — both exact. (Note `Encoding.lean:43` cites
    the adjacency *matrix* for p. 112 / Def 6.14; that is a different passage and is also
    right. No conflict.)
  - The arithmetic: `n + 5 < 10n ⟺ 5 < 9n ⟺ n ≥ 1` ✓, and it does mean what the file says —
    `2ⁿ/(n+5) ≥ 2ⁿ/(10n)`, so our achievable `S` is the **larger** number. The plan's old
    prediction really was backwards, and `:45–48` reports the reversal correctly.
  - The encoding accounting at `:41–44` matches `Encoding.lean:103–105` exactly: a leaf is
    `false :: sign :: unaryBits idx`, i.e. `idx + 3` bits; a gate is tag + connective + one
    continue bit per child + the children + a stop bit, i.e. "three bits plus one per child".

  **What is wrong is the comparison built on them.** The paragraph names only the two
  effects that push our count *up* (every literal occurrence is a node; no gate is reused)
  and omits the one that pushes it *down*: `Circuit.size` charges **1** for an
  unbounded-fan-in gate where Def 6.1 charges `k − 1` fan-in-2 vertices. With that effect
  restored, the two families are genuinely **incomparable at small `S`**, not nested:

  > Witness, verified in Lean against this repo's own definitions:
  > `and3 : Circuit 3 := .node true [.lit ⟨0,true⟩, .lit ⟨1,true⟩, .lit ⟨2,true⟩]` has
  > `and3.size = 4` (`simp [Circuit.size]`) and `and3.eval x = (x 0 && x 1 && x 2)`.
  > Under Def 6.1 the same function needs `≥ 5` vertices: the graph *has* 3 sources, each
  > needs an outgoing edge (only one vertex may be a sink), and with `g` fan-in-2 gates the
  > edge count forces `2g ≥ 3 + (g − 1)`, so `g ≥ 2` and `|C| ≥ 3 + 2 = 5`.
  > So `AND₃` lies in {computed by a tree of size ≤ 4} and **not** in {computed by an AB
  > circuit of size ≤ 4}. AB's conclusion at `S = 4, n = 3` therefore does **not** imply
  > ours, and ours "rules out" a family AB's does not even contain. At `n = 3, S = 4` AB's
  > family is in fact *empty* while ours is not.

  The correct statement is the additive one the paragraph is reaching for: a size-`S` tree
  converts to a Def-6.1 DAG of size at most `S + 2n` (each `k`-ary gate becomes `k − 1`
  binary gates, total `S − 1 − g` of them, plus `n` sources and at most `n` shared `¬`
  gates). So trees of size `S` ⊆ DAGs of size `S + 2n`, the reverse fails badly, and at the
  `S ≈ 2ⁿ/n` that matters the `2n` is negligible — AB's is the stronger theorem *there*, but
  not "at any `S`". That is also exactly what line 31's own bolded "the two are not
  comparable" says, so the paragraph currently asserts both "not comparable" and "weaker at
  any `S`" four lines apart. A reader cannot act on it, and U11's whole framing is "our
  constant, not AB's".

  → Replace `:37–39` with: our `Circuit.size` charges a node for every literal occurrence
  and reuses nothing, but charges only `1` for a `k`-ary gate where Def 6.1 charges `k − 1`;
  a size-`S` tree embeds in a DAG of size `≤ S + 2n` and the reverse fails, so the two
  conclusions are incomparable at small `S` and AB's is strictly the stronger one at the
  `S ≈ 2ⁿ/n` in play. Keep `:31` and `:41–48` as they are.

  **Consistency with U9.** No conflict with the book, and none between the two accounts:
  U9's cites p. 46's ∧/∨-**symbol** convention for Claim 2.13, U10's cites Def 6.1's
  **vertex** count for Thm 6.21, and each has cited the right convention for its own
  theorem. But they share a defect — this is the *same* one-sided accounting that this log
  ruled Blocking at `Universal.lean:39–46` in U9 round 1, on the same pair of models, and
  the orchestrator's freshly-corrected `NOT_FORMALIZED.md:27` now states the two-sided
  version ("`Circuit.size` charges `1` per unbounded gate but pays for every literal
  *occurrence*") **eleven lines above** where the same file states the one-sided version.

- [Blocking] `ch6/NOT_FORMALIZED.md:76–79` — the rewritten closing paragraph carries the
  same false claim ("quantifies over a **far smaller family** than AB's fan-in-2 DAGs with
  shared sources") and, as noted above, contradicts this same file's own `:27`. The
  paragraph's first half (`:73–75`, the reversal of the prediction) is correct and reproduces
  — keep it. → Fix `:76–79` in step with `HardFunctions.lean:37–39`.

- [Blocking] `ch6/PLAN.md:139` — "'Computed by no circuit of size `≤ S`' therefore excludes a
  **far smaller family** than AB's" — same claim, same fix. Note `:140` ("a function hard for
  size-`S` trees need not be hard for size-`S` DAGs") is **true** and should be kept; it is
  `:139`'s universal that fails. `:135–138` and `:143–145` are correct as written.

### Advisory

- [Advisory] `TCSlib/Complexity/CircuitComplexity/HardFunctions.lean:54–56` — this paragraph
  is now **stale**, and it was never a divergence from AB. It reports that
  "`ACP.size_le_length_encodeSigma`, the hook `ch6/PLAN.md` names, bounds a circuit's size by
  its encoding's length", but the orchestrator has since corrected `ch6/PLAN.md:143–145`,
  which now names `length_encodeCircuit_succ_le` and says precisely this. A module docstring
  under the heading `## Divergences from [AB09, Thm 6.21]` is the wrong place for a note
  about a planning file, and item 0's exemption covers AB divergences, not project
  bookkeeping. (It costs 3 of the 19 non-exempt lines, so no cap is breached either way.)
  → Delete `:54–56`; the correction is recorded in the plan and in this log.

- [Advisory] `TCSlib/Complexity/CircuitComplexity/HardFunctions.lean:11–62` — the module
  docstring has no `## Main definitions` section. It is the **only one of the eleven files**
  in `CircuitComplexity/` without one, and `policy.md` §1 and rubric item 6 both name that
  section. Not raised as Blocking because the file has no public definitions (its one `def`
  is `private`), so the section would be empty. → Either add a one-line "none — this file
  adds only theorems", or leave it and accept the deviation knowingly.

- [Advisory] `TCSlib/Complexity/CircuitComplexity/HardFunctions.lean:253–255` — "at `n = 3`
  it excludes every single-literal circuit" undercounts. `Circuit.size (.node _ []) = 1`
  (verified), so the size-`1` circuits are the `2n` literals **and** the two empty gates, the
  constant `1` and the constant `0`. → "every literal and both empty gates".

- [Advisory] `ch6/PLAN.md:125` and the rewritten U10 section — the section records the
  constant and the model divergence but not the **vacuity range**, and `:125` still states
  the target as "For `n > 1`". U11 consumes `exists_not_eval_of_lt` at some `ℓ` and needs to
  know the bound has no content below `ℓ = 3`. → Add one clause. Worth recording alongside
  it: AB's own `2ⁿ/(10n) ≥ 1` first at `n = 6`, so AB's statement is vacuous for `n ≤ 5`
  where ours is vacuous only for `n ≤ 2`. Our earlier onset is a consequence of the larger
  constant and is *not* a defect.

- [Advisory] `TCSlib/Complexity/CircuitComplexity/HardFunctions.lean:135` — `(n + 4)` is
  forced only by `n = 0`. Rerunning the induction by hand, `(n + 3)` closes for every
  `n ≥ 1`: the leaf case needs `k + 4 ≤ n + 3`, true since `k ≤ n − 1` (tight at
  `k = n − 1`), and the gate case needs `4 ≤ n + 3`. At `n = 0` the gate case needs
  `4 ≤ n + 3` and fails, and `(0+4)·1 = 4` is met with equality by `.node b []`. So the
  constant is genuinely tight for this serialiser at `n = 0` and off by one above it; `n + 3`
  would hand U11 `2^ℓ/(ℓ+4)`. Not required — the file claims only `≤`, and nothing downstream
  needs the better constant.

- [Advisory] `TCSlib/Complexity/CircuitComplexity.lean:52–53` — the `## Contents` bullet reads
  "computed by no circuit of size `2 ^ n / (n + 5)`"; the theorem is `size ≤ 2^n/(n+5)`.
  → "of size at most". (AB's own phrasing is equally loose, so this is cosmetic.)

- [Advisory] full build is **3698 jobs**, not the 3697 claimed. 3697 is the progress-line
  index `[3697/3698]`, not the total. The tree is not warning-free — `LearningTheory/Hedge.lean`
  and `LearningTheory/JohnsonLindenstrauss/Rademacher.lean` emit linter warnings — but no
  warning comes from any ch6 file.

### Checked and correct — dropped, not carried forward

- **The counting argument is sound end to end, and was checked against the real serialiser,
  not an assumed shape.** `length_encodeCircuit_succ_le` (`:135`) is proved through
  `encodeCircuit_node`, `encodeChildren_nil` and `encodeChildren_cons`
  (`Encoding.lean:112, 117, 122`), which are themselves proved from `encodeCircuit` at
  `Encoding.lean:103–105`. Hand-replayed: the leaf case needs `k + 4 ≤ n + 4` with
  `k < n`; the side induction gives `|encodeChildren ds| ≤ (n+4)·Σsize + 1`, the `+1` of
  slack paying for each child's continue bit; the gate case then needs `4 ≤ n + 4`. The
  one-bit slack really is what makes it close — without it the cons step is off by one.
- `encodeCircuit_injective` (`:163`) — sound: `readCircuit_encodeCircuit` at full fuel with
  empty remainder gives `some (C, [])` for both, `rw [h]` identifies the two parser calls,
  and `Option.some` injectivity finishes.
- `private bitsToNat` (`:76`) — **Blocking item 4 is not triggered.** A full sweep of
  Mathlib, Batteries and Lean core confirms U10's report. The only two `List Bool → ℕ`
  functions in Mathlib are `Computability.decodeNat` (`Computability/Encoding.lean:110`) and
  `unaryDecodeNat`; `decodeNat` has round-trip lemmas in the `encodeNat` direction only
  (`decode_encodeNat`, `:131`) and **is not injective** — `decodeNat [false] =
  decodeNat [false, true] = 2`. `Encodable.encode` on `List Bool` is injective but its only
  size lemma is `Encodable.length_le_encode` (`Logic/Equiv/List.lean:87`), a *lower* bound;
  because `encodeList` goes through `Nat.pair` it grows like `4 ^ length`, so a `< 2^length`
  bound is not merely absent but **false**. `Nat.bits` (`Data/Nat/Bits.lean:151`) is the
  wrong direction and has no inverse in Mathlib; `Nat.ofBits` exists only in *Batteries*
  (`Batteries/Data/Nat/Basic.lean:112`) over `Fin n → Bool`, with a bound
  (`ofBits_lt_two_pow`) but no injectivity lemma and a dependent domain; `BitVec.ofBoolListLE`
  has neither `toNat_ofBoolListLE` nor injectivity. `bitsToNat` is a three-line wrapper over
  `Nat.ofDigits 2` with a sentinel `1`, discharged by `Nat.ofDigits_lt_base_pow_length` and
  `Nat.digits_ofDigits` — that is reuse of the only Mathlib lemmas that exist, not
  redefinition. **Keep as is.**
- **Vacuity (Blocking item 3) — not triggered.** `(n+4)·S < 2ⁿ` does force `S = 0` for
  `n ≤ 2` (`4S<1`, `5S<2`, `6S<4`), and `Circuit.size` is never `0` (`.lit → 1`,
  `.node → 1 + …`), so `:50–52` is accurate. Both `example`s compile. The `n = 3` one
  genuinely exercises `S = 1`: `2^3/(3+5) = 1` (verified), `norm_num` reduces the hypothesis
  to `C.size ≤ 1`, and size-`1` circuits exist, so the instance is not degenerate. Sanity
  check on the content: `2^(2^3) = 256` functions against `2^((3+4)·1) = 128`, and the eight
  size-`1` circuits compute at most eight functions. Dropping AB's `n > 1` is harmless — see
  the advisory above.
- **`Set.ncard` is the right interface for U11.** `{f | ∃ C : Circuit n, C.size ≤ S ∧
  C.eval = f}` quantifies over the infinite `Circuit n`, so `DecidablePred` is unavailable
  without `Classical`, and putting a `Classical.dec` instance in a *statement* would leak an
  implementation choice into U11's API. `Set.ncard` needs none, and it composes with
  `Set.ncard_univ` / `Nat.card` — which is exactly how `exists_not_eval_of_lt:227` uses it.
  A consumer wanting a `Finset` has `Set.Finite.toFinset`; the set is finite for free inside
  a `Fintype`. Endorsed.
- **`length_encodeCircuit_succ_le` does belong in `Encoding.lean` — agreed, queue it.** It is
  the exact converse of `size_le_length_encodeCircuit` (`Encoding.lean:341`), a fact about
  that serialiser and nothing else, and the two are proved by the same side induction over
  the children list. Moving it also **deletes `length_encodeCircuit_lit` (`:112–123`)
  outright**: inside `Encoding.lean` the leaf length is `simp [encodeCircuit, unaryBits]`,
  where here it costs an 11-line induction on the index purely to avoid naming a `private`
  def. → **Cross-track pass**, together with the three `Circuit.eval_*` relocations already
  queued.
- **The `private` on `unaryBits` (U8's instruction) was not wrong.** `policy.md` §1 says to
  mark internal helpers `private`, and `unaryBits` is one. The workaround at `:112–123` is
  not evidence against the `private`; it is evidence that the *lemma is in the wrong file*.
  Relocating `length_encodeCircuit_succ_le` removes the need to export anything, which is
  strictly better than widening `Encoding.lean`'s surface with `unaryBits` or a
  `length_unaryBits` that would then have exactly one consumer. → Keep `private`; fix by
  relocation.
- **Orchestrator's own edits.** Aggregator registration at
  `TCSlib/Complexity/CircuitComplexity.lean:13` with a `## Contents` bullet at `:52–53` —
  correct and in position (import order matches the bullet order); `ch6/PLAN.md:122` U10 →
  `WIP` — correct; `ch6/PLAN.md:143–145`, the `size_le_length_encodeSigma` correction —
  **verified right**: `size_le_length_encodeSigma` is `C.2.size ≤ (encodeSigma C).length`
  (`Encoding.lean:363`), which bounds size by length, and the count needs length bounded by
  size. `ch6/PLAN.md:153`, telling U11 the constant is `2^ℓ/(ℓ+5)` with the parametric hook
  `ACP.exists_not_eval_of_lt` — correct on both counts. The three Blocking items above are
  the only defects in the rewrite, and two of them are propagations of the first.
- **The file never implies it proves AB's `2ⁿ/(10n)`.** `10 n` appears exactly twice
  (`:31`, `:45`), once to disclaim it ("is not proved here") and once inside the arithmetic;
  `:47–48` states "That is not a strengthening of AB" explicitly. Nothing in
  `## Main results` or in any declaration docstring attributes AB's constant to this file.

### Ruling on the divergence account

The reversal U10 reports is **real and correctly argued**: `2ⁿ/(n+5) > 2ⁿ/(10n)` for every
`n ≥ 1`, the arithmetic is right, the direction means what the file says, and the mechanism
(a unary index costs `n` bits a leaf against AB's `9 log S ≈ 9n` a gate) checks out against
both the serialiser and AB p. 115. The plan's old prediction was indeed backwards, and
flagging that rather than quietly restating it is the right instinct.

The *second* claim — that the theorem is weaker anyway, for a model reason — is **half
right and stated too strongly**. The model gap is real and the reading of Def 6.1 is exact,
but the account lists only the effects that make our circuits expensive and omits the one
that makes them cheap, and the conclusion drawn from that one-sided list ("a
correspondingly weaker conclusion at any `S`") is false at small `S`, contradicts the same
paragraph's opening, and does not survive the `AND₃` witness. Fix the paragraph to the
additive `S + 2n` form and the claim becomes true, sharper, and consistent with `:31`.

**Verdict: REVISE.** Three Blocking items, all of them the same prose defect in the file and
its two ledger copies; nothing wrong with any theorem, any proof, or any constant. Sixteen
rounds, sixteenth time the only Blocking findings are prose, still never a false theorem.

`ch6/PLAN.md` U10 left at `WIP`.

*Addendum, on the scratch-file rule added to `ch6/REVIEW_CRITERIA.md:110–115` mid-round:*
this round's `#print axioms` was re-run from `u10_axioms.lean`, written immediately before
the check, after the rule landed. All five results are byte-identical to the first run, and
the same file also carries U10's `AND₃` witness (`size = 4`, `eval x = x 0 && x 1 && x 2`),
`2^3/(3+5) = 1`, `2^2/(2+5) = 0` and `(Circuit.node true []).size = 1` — whole file, exit 0.

---

## U9 — round 2 — REVISE

**`Universal.lean` itself is clean this round — the single Blocking is in
`ch6/NOT_FORMALIZED.md:27`, which was rewritten to fix round 1's Blocking and acquired a
new arithmetic error doing it.** The unit's file needs no further work; the flip to `DONE`
follows as soon as that one ledger row is corrected.

### No Lean changed — verified, not accepted on report

`git diff HEAD` on the file is **+18 −8, entirely inside the module docstring**. Extracting
everything from `set_option maxHeartbeats` to EOF from both `HEAD` and the working tree
gives **108 lines each, `diff` empty** — byte-identical. The mathematics verified in round 1
carries over untouched. `code=76` in the `awk` count is unchanged from round 1, consistent.
Independently re-run anyway, under unit-numbered scratch names per the new rule (and none of
my round-1 scratch files were reused):

- `lake build` (full) — **3698 jobs, exit 0** ✓ matches.
- `lake build ...Universal` — **916 jobs, exit 0**.
- `lake build TCSlib.Complexity.CircuitComplexity` — **3044 jobs, exit 0** (3043 → 3044 with
  `HardFunctions` now in the aggregator import list).
- `zsh scripts/lean_check.sh` — no output, rc 0.
- `#print axioms` re-run on all **11** public declarations: all
  `[propext, Classical.choice, Quot.sound]`, `ACP.minterm` depends on none. **No `sorryAx`.**
  `grep sorry` empty. 13 declarations (11 public, 2 private) at lines 81–174.
- Mandated `awk`, verbatim:

  ```
  total=177 code=76 comment=81 blank=20
  ```

### The line-count arithmetic — checked, all of it reproduces

Spans read off the file: docstring `10–68` = **59**; `## Divergences` `32–54` = **23**;
`## References` `64–67` = **4**; exempt = 27; non-exempt = 59 − 27 = **32** ✓. Whole-file
comment after exemption = 81 − 27 = **54**, against `code=76` ✓. Divergences 21 → 23 ✓, and
the two added lines are exactly the two closed forms, which is the stated reason. 32 is
under the ~40 cap. Every figure the unit reported is correct.

The exemption is now clean, which is what Advisory A1 asked: `32–54` is wholly divergence
content, and the reuse rationale sits under its own `## Implementation notes` (`56–62`,
7 lines) *inside* the non-exempt 32. Correct call, and `## Implementation notes` is the
Mathlib-standard heading for it.

### The table — checked independently, closed forms and instances both

I did not take the closed forms on trust; I re-derived each from the construction and then
proved the derivation in Lean as an identity in `n` and `p := 2ⁿ`, and the instances by
`decide`. All proved:

| row | derivation from the construction | closed form | proved |
|---|---|---|---|
| AB symbols | `2ⁿ` clauses × `(n−1)` `∨` + `(2ⁿ−1)` `∧` | `(n−1)2ⁿ + (2ⁿ−1) = n·2ⁿ − 1` | ✓ identity |
| AB Def 6.1 vertices | `n` sources + `n` `¬` + `(n−1)2ⁿ` `∨` + `(2ⁿ−1)` `∧` | `n·2ⁿ + 2n − 1` | ✓ identity |
| `Circuit.size` | `n·2ⁿ` leaves + `2ⁿ` minterm gates + 1 top | `2ⁿ(n+1) + 1` | ✓ identity |
| excess over symbols | row 3 − row 1 | `2ⁿ + 2` | ✓ identity |

Instances `(1,3,5,4)`, `(7,11,13,6)`, `(23,29,33,10)`, `(63,71,81,18)` all `decide`. Row 3 was
additionally checked against the **real construction** rather than the closed form:
`(universalCircuit (fun _ : Fin k → Bool => true)).size` elaborates to `5, 13, 33, 81` for
`k = 1,2,3,4` — and at `k = 3` also straight off `universalCircuit_size` rather than off
`universalCircuit_const_true_size`, so the row is not merely restating one theorem.

To the coordinator's worry that four instances can agree for the wrong reason: they cannot
here, because the closed forms were derived from the construction first and then *proved*
as identities in `n`, not fitted to the four points. The one place the instances did
independent work is flagged in the Blocking below — they are what falsifies the ledger row.

### The prose — says what the table shows, on all four counts asked

- `:39–40` "`n2ⁿ` is not an artifact of Chapter 2's convention — it holds under both of
  AB's." ✓ Exactly the correction round 1 demanded, stated as the lead.
- `:46` "`Circuit.size` measures a different object: nodes of an unbounded-fan-in *tree*." ✓
  The divergence is now located where it actually is.
- `:50–51` "a `k`-ary gate costs `1` here where AB's fan-in-2 expansion costs `k-1`, a
  saving large enough that the net excess over `n·2ⁿ - 1` is only `2ⁿ + 2`." ✓ The
  load-bearing downward effect is named and is tied to the number. It declines to assert my
  rough counterfactual `2n·2ⁿ`, which is the better choice — that figure was an estimate,
  and the file should not assert estimates.
- `:49–50` "The leaves alone already come to within one of AB's whole symbol count, so they
  are not what pushes us over." ✓ and literally exact: `n·2ⁿ` against `n·2ⁿ − 1`, difference
  proved `= 1`.
- `:47` "(nothing is shared, and a sign rides on the leaf instead of a `¬` gate)" — a good
  addition not asked for: it is why our tree has no `¬` nodes to set against AB's, which the
  reader would otherwise miss. True of `Basic.lean:80–88` (`Lit` carries `sign`; `Circuit`
  has no negation constructor).

Round 1's Blocking B1 is **fully addressed**. Both defects are gone: the manufactured
AB-versus-AB contrast, and the unearned "therefore".

### The `¬`-gate hedge — ruling: true, but misplaced, and it does not propagate

Advisory, not Blocking: nothing false is asserted. But the hedge does not buy accuracy where
it is placed, and two things around it are inconsistent with it.

The sentence has already fixed its scope at `:40` — "On `2ⁿ` clauses of `n` literals", the
full CNF, AB's worst case. Inside that scope the count is **exactly** `n`, not "at most `n`":
`C_v` contains `z̄_i` iff `v_i = 1`, and over all `2ⁿ` assignments some `v` has `v_i = 1` for
every `i`, so every variable is read negated and needs its gate; fan-out is unbounded under
Def 6.1, so one gate per variable suffices. The case the hedge guards — "a variable never
read negated" — is a smaller `f`, which the sentence excluded two lines earlier. Then:

- `:44` concludes "so `n·2ⁿ + 2n - 1` *vertices*", flatly. If "at most" were doing work the
  conclusion would have to read "at most `n·2ⁿ + 2n - 1` vertices". The hedge is dropped
  before it reaches the number it qualifies.
- The table's row 2 gives `3, 11, 29, 71`, which are the exactly-`n` counts. The table
  treats as exact the quantity the prose hedges.

And the hedge is applied to the one term that *is* exact while `(n-1)2ⁿ` is left flat — yet
that is the term a cleverer DAG could genuinely shrink (prefix-sharing the clause `∨`-trees
across clauses brings the full CNF to ≈`3·2ⁿ` vertices, well under `n·2ⁿ`). `(n-1)2ⁿ` is
nonetheless right *as a description of AB*, since it is AB's own stated conversion — p. 107–108,
"a ∨ or ∧ gate with fan-in `f` can be easily repaced with a subcircuit consisting of `f − 1`
gates of fan-in 2" — applied gate by gate.

→ Drop "at most" (the scope already pins it), and if a caveat is wanted put it where it
belongs: one clause noting `(n-1)2ⁿ` is AB's own gate-by-gate fan-in-2 conversion, not a
claim that no smaller DAG exists. Avoiding a second unearned "exactly" was the right
instinct; it was aimed at the wrong term.

### Advisories from round 1 — both addressed, dropped

- **A1** (reuse rationale inheriting item 0's exemption) — fixed as described above. Dropped.
- **A2** (the phantom fourth reuse reason) — the file gives exactly three reasons at `:58–62`,
  all three re-verified in round 1, and the fourth was **not** added. Confirmed independently
  this round: `TCSlib/Complexity/CircuitComplexity/PPoly.lean:7` does import
  `TCSlib.BooleanAnalysis.RazborovSmolensky.ACpGates`, so the reason would have been false;
  and `BoolCircuit.Lit.toLiteral` is at `LMN/NormalFormConversion.lean:29`, not
  `CircuitHelpers.lean`. Withdrawing rather than restating is the right call. Dropped.
- The glob claim is gone — `grep glob` over `Universal.lean`, `ch6/PLAN.md` and
  `ch6/NOT_FORMALIZED.md` returns nothing. Dropped.

### Round 1 Blocking B2 — `ch6/PLAN.md` skip list — FIXED

`:101` now reads "Exercise 6.1's sharper `O(2ⁿ/n)` bound | A different and harder
construction than Claim 2.13's; nothing in range needs it. (**Claim 2.13 itself is no longer
skipped** — Theorem 6.22 needs it, so U9 proves it in `Universal.lean`.)" The contradiction
with `:111` and `:143` is gone, and the parenthetical means a later reader cannot re-derive
the old skip. Correct, and better than what I asked for. Dropped.

### Blocking

- [Blocking] `ch6/NOT_FORMALIZED.md:27` — **the rewritten row attaches the `2ⁿ+2` excess to
  the wrong baseline, and then draws the opposite of the right conclusion from it.** The
  false "∧/∨ symbols on a fan-in-2 DAG with shared sources" is correctly gone, and the row
  now separates the two conventions properly — but the sentence

  > "Counting AB's own CNF gives `n·2ⁿ + 2n - 1` vertices against our `2ⁿ(n+1)+1` — an excess
  > of exactly `2ⁿ+2`, and it comes from the gate nodes, not the leaves."

  sets `2ⁿ+2` against the **Def 6.1 vertex** count. It is the excess over the **∧/∨ symbol**
  count. Against vertices the excess is `2ⁿ − 2n + 2`. Proved by `decide` on the row's own
  four instances:

  | n | size | AB vertices | size − vertices | `2ⁿ+2` |
  |---|---|---|---|---|
  | 1 | 5 | 3 | **2** | 4 |
  | 2 | 13 | 11 | **2** | 6 |
  | 3 | 33 | 29 | **4** | 10 |
  | 4 | 81 | 71 | **10** | 18 |

  The row's own numbers refute it at every one of the four points, `2ⁿ+2` agreeing with
  nothing in the column it is attached to.

  The trailing clause then inverts: **against the vertex baseline the excess comes from the
  leaves, not the gate nodes.** Our leaves `n·2ⁿ` against AB's `n` sources + `n` `¬` is
  `+(n·2ⁿ − 2n)`; our `2ⁿ+1` gates against AB's `n·2ⁿ − 1` is `−(n·2ⁿ − 2ⁿ − 2)`; net
  `2ⁿ − 2n + 2`. "Gate nodes, not leaves" is true only against the **symbol** baseline, which
  is the baseline the docstring uses and states (`Universal.lean:51`, "the net excess over
  `n·2ⁿ - 1`") and the one this row dropped.

  The pattern is round 1's, in the same row: the docstring keeps two baselines apart and the
  ledger collapses them into one. Round 1 collapsed the two *conventions*; round 2 collapses
  the two *baselines*. The docstring is right both times.

  → Attach the number to its baseline. E.g.: "Counting AB's own CNF gives `n·2ⁿ − 1` ∧/∨
  symbols (p. 46's Chapter-2 convention) and `n·2ⁿ + 2n − 1` Def 6.1 vertices, against our
  `2ⁿ(n+1)+1`. Our `n·2ⁿ` literal leaves come to within one of AB's whole symbol count, so
  the `2ⁿ+2` excess over it is the gate nodes." Or drop the mechanism entirely and point at
  `Universal.lean`'s `## Divergences`, which now states it correctly — the ledger does not
  need to re-derive it, and re-deriving it is what has gone wrong twice.

  (Minor, in the same row, not separately raised: "it happens to equal our leaf count" is
  exact if `n2ⁿ` is read as AB's quoted round figure and off by one against the exact
  `n·2ⁿ − 1`. The docstring's "within one" is the safer phrasing. And the new "**Not
  formalized:** Exercise 6.1's sharper `O(2ⁿ/n)`" does satisfy the `PARTIAL` legend at `:7`,
  so round 1's third Advisory is addressed.)

### Verdict

**REVISE** — one Blocking, in an orchestrator-owned ledger file. To be unambiguous about
where the work is: **`TCSlib/Complexity/CircuitComplexity/Universal.lean` passes.** Round 1's
Blocking B1 and both Advisories are properly fixed, the rewritten account is correct and its
table verified independently down to Lean-proved identities, no Lean changed, 11 declarations
`sorry`-free, all three builds green, every reported measurement reproduces. The one
substantive judgment call left in the file — the `¬`-gate hedge — is Advisory and costs a
word.

Sixteen rounds; every Blocking finding to date has been prose asserting more or other than
the code does, and this one is the fourth that is outright false. Still never a false
theorem. Worth noting where the defects now live: the unit's own file has been clean of
Blocking findings since its rewrite, and both of this round's and last round's remaining
Blocking findings are in the ledger files that *summarise* it. The summaries are now the
weak point, and the cheapest fix is for them to cite the docstring rather than restate it.

`ch6/PLAN.md` U9 left at `WIP`; flip to `DONE` once `NOT_FORMALIZED.md:27` is corrected —
no further review of `Universal.lean` is needed for that.

---

## U10 — round 2 — PASS

All three round-1 Blocking items are addressed — the docstring rewrite and **both** ledger
propagations. Zero Blocking. Four advisories closed, three minor ones raised.

### The prose-only claim — verified two independent ways

`awk` (rubric item 7's mandated command) on the revised file:

```
total=274 code=140 comment=113 blank=21
```

`code=140` is **identical to round 1**, and `git diff -U0` confirms it structurally rather
than by coincidence: 20 insertions, 12 deletions, and **every hunk falls inside a `/-! … -/`
block** — the module docstring (`:17–19`, `:35`, `:40–48`, `:57–60`, `:64`) and the
degenerate-arities section comment (`:263`). Not one line of Lean changed. Claim upheld.

### Measurements

| claim | reproduced |
|---|---|
| module build 1030 | **1030 jobs, success** ✓ |
| aggregator 3044 | **3045 jobs, success** — see A2 |
| full build 3699 | **3699 jobs, success** ✓ |
| `lean_check.sh` exit 0 | **zero diagnostics, exit 0** ✓ |
| five public decls, no `sorryAx` | ✓ all `[propext, Classical.choice, Quot.sound]` |
| `awk total=274 code=140 comment=113 blank=21` | ✓ exact |
| docstring 61 / Divergences 34 / Refs 4 / **23 non-exempt** | docstring **60** (`:11–70`), Divergences **33** (`:33–65`), Refs 4 (`:66–69`) — see A1; **23 non-exempt confirmed** |

Re-verified from `u10r2_check.lean` / `u10r2_count.lean`, both written immediately before
the check per `REVIEW_CRITERIA.md:110–115`; the round-1 scratch file was removed first.

### Ruling on the rewrite

- **`:35` no longer contradicts the body.** It now reads "the two **statements** are not
  comparable", and the body's "at the `S ≈ 2 ^ n / n` in play AB's conclusion is strictly
  the stronger — but not at every `S`" is exactly the local refinement of that global
  incomparability. Both directions are now present: the two effects that raise our count and
  the one (`1` per `k`-ary gate against Def 6.1's `k − 1`) that lowers it. This was the
  Blocking finding; it is resolved, and resolved by the right mechanism rather than by
  deleting the claim.
- **The closing disclaimer is correct.** "Neither comparison is formalized; both describe
  the gap to AB, not anything proved below" — checked, not assumed: `DAG` and `vertex` occur
  in the file **only** at `:36`, `:38`, `:43`, all inside the module docstring, and every one
  of the five theorems and both `example`s quantifies over `Circuit n` with `Circuit.size` /
  `Circuit.eval` / `encodeCircuit` and nothing else. No DAG circuit type exists anywhere in
  TCSlib (`NOT_FORMALIZED.md` §6.2 records that), so nothing below *could* depend on either
  comparison.
- **`S + 2 * n` vs the derivation's `S + 2n − 1`: the docstring's figure is the correct one,
  and the discrepancy is not slack — it is load-bearing.** The derivation is sound as far as
  it goes: a tree with `S` nodes has `S − 1` edges, so `Σ kᵢ = S − 1` over the `g` gates, and
  a `k`-ary gate becomes `k − 1` fan-in-2 gates, giving `Σ(kᵢ − 1) = S − 1 − g`, plus `n`
  sources and at most `n` shared `¬` ⇒ `S + 2n − 1 − g`. **But it assumes every gate has
  arity ≥ 1.** `Circuit.node b []` has arity `0`, and Def 6.1 has no constant gate at all —
  only fan-in-2 `∨`/`∧` and fan-in-1 `¬` — so the `k − 1` accounting breaks there.
  Counterexample to the tighter figure: `node true []` on `n = 1` has `S = 1, g = 1`, so the
  derivation yields `1` vertex, whereas the constant `1` genuinely needs three (`x₁`, `¬x₁`,
  `x₁ ∨ ¬x₁`) — and `S + 2n = 3` holds **with equality**. So `S + 2 * n` is both correct and
  tight at that point. → **Do not tighten `S + 2 * n` to `S + 2n − 1` in a later round**;
  this entry is the reason.
- **The `AND₃` witness re-verified**, and the formalizer's report about the proof is right:
  `simp [Circuit.eval, Lit.eval]` leaves a reassociation goal and `Bool.and_assoc` closes it.
  `size = 4` and `eval x = (x 0 && x 1 && x 2)` both check. The "at `S = 4` AB's family is
  empty" clause also holds under the natural reading of Def 6.1 ("one sink"): with `≤ 4`
  vertices and 3 sources there is at most one gate, so some source has no outgoing edge and
  is a second sink. The claim survives even under a laxer reading, since one fan-in-2 gate
  cannot compute a 3-variable `AND`.

### Ruling on the four advisories

- `:54–56` stale paragraph **deleted** ✓ — the `ch6/PLAN.md:143–145` correction stands on its
  own and the docstring no longer reports it as outstanding.
- `## Main definitions` **added** at `:17–19` ✓. Closed.
- `:263` now "every literal and both empty gates" ✓, and the count checks: every circuit has
  `1 ≤ size`, a gate with at least one child has `2 ≤ size`, and `Fin 3 × Bool` has 6
  elements — so the size-`1` circuits on `Fin 3` are exactly 6 literals + 2 empty gates = 8.
- **`(n + 3)` declined — correct call, endorsed.** Adopting it means a `0 < n` hypothesis on
  `length_encodeCircuit_succ_le` that propagates to `card_computable_le`,
  `exists_not_eval_of_lt`, `exists_hard_function` and thence to the one declaration U11
  consumes parametrically. Mathematically the hypothesis is free (the statement is already
  vacuous for `n ≤ 2`), which is precisely why it is not worth having: it is pure API
  pollution bought for a move from `2ⁿ/(n+5)` to `2ⁿ/(n+4)`, both `Θ(2ⁿ/n)` and neither
  AB's. The one-line reason at `:57–60` is accurate — verified in Lean that
  `.node b []` meets `(0 + 4) * 1` with equality, so `n = 0` really is what forces the `4`.
- The extra line at `:64`, "AB's own `2 ^ n / (10 n)` is below `1` until `n = 6`" — arithmetic
  confirmed in Lean: `2^5 / (10*5) = 0` and `2^6 / (10*6) = 1`. It earns its one line: it
  stops a reader reading our `n ≤ 2` vacuity as a defect, when AB's own theorem is vacuous
  three values further out.

### Advisory

- [Advisory] `TCSlib/Complexity/CircuitComplexity/HardFunctions.lean:11–70` — the reported
  docstring total (61) and `## Divergences` span (34) are each **one line high**; measured,
  they are 60 (`:11–70`) and 33 (`:33–65`). The two errors are in the same direction and
  cancel, so the figure that matters — **23 non-exempt**, against a ~40 cap — is right. Raised
  only because item 7 exists to stop counts that do not reproduce. → Count `/-!` and `-/` once.
- [Advisory] the aggregator is now **3045 jobs**, not the 3044 reported; `Universal.lean` was
  rebuilt between the two runs, so U9's round-2 edit landed in between. Benign cross-track
  drift, same cause as the 3698 → 3699 move on the full build, and neither figure is a
  property of this unit. → Job counts are only meaningful alongside the timestamp of the run.
- [Advisory, re-raised from round 1, unaddressed] `ch6/PLAN.md:125` still states the target as
  "For `n > 1` some `f` …", and the rewritten U10 section still records no **vacuity range**.
  U11 consumes `exists_not_eval_of_lt` at some `ℓ` and needs to know the bound has no content
  below `ℓ = 3`. One clause. (Orchestrator-owned; not a bar to this unit.)
- [Not a finding, noted for precision] `:19` says the file "adds only theorems"; it does carry
  one `private def bitsToNat`. A private helper is by construction not a *main* definition, so
  the section is correct as a `## Main definitions` entry.

### Carried forward, unchanged, to the cross-track pass

Per the orchestrator's instruction none of these were acted on, and none is a defect in this
file: relocate `length_encodeCircuit_succ_le` into `Encoding.lean` (it is the exact converse
of `size_le_length_encodeCircuit` and its move deletes `length_encodeCircuit_lit` outright);
`unaryBits` stays `private` (the workaround is evidence the lemma is in the wrong file, not
that the def should be exported); `bitsToNat` stays (verified in round 1 to be minimal glue
over `Nat.ofDigits 2`, with no Mathlib, Batteries or core equivalent); `Set.ncard` stays.

### Verdict

**PASS.** Zero Blocking. The one Blocking defect of round 1 was prose, and the fix is prose —
`code=140` on both sides, with the diff confined to comment blocks, so no theorem, proof or
name moved. Seventeen rounds; the only Blocking findings have been prose in all seventeen,
and there has still never been a false theorem.

`ch6/PLAN.md` U10 flipped to `DONE`.

---

## U9 — round 3 — PASS

Zero Blocking. `ch6/PLAN.md` U9 flipped to `DONE`.

### Measurements — all re-run, all reproduce

- `lake build` (full) — **3699 jobs, exit 0** ✓ (`NCAC` now registered). Only warning in the
  whole build is the pre-existing `Hedge.lean:374` unused-variable linter hit.
- `lake build ...Universal` — **916 jobs, exit 0** ✓ (stable across all three rounds).
- `lake build TCSlib.Complexity.CircuitComplexity` — **3045 jobs, exit 0**.
- `zsh scripts/lean_check.sh` — no output, **exit 0** ✓.
- `#print axioms` on all **11** public declarations: all `[propext, Classical.choice,
  Quot.sound]`, `ACP.minterm` depends on none. **No `sorryAx`.** `grep sorry` empty.
- All **five** degenerate checks recompile: `n = 0` with `f ≡ true` → size 2; `f ≡ false` →
  size 1 *and* the circuit `= .node false []` by `exact`; `minterm` at `n = 0` → size 1;
  `minterm_eval_zero`. Plus the bound attained at `n = 1,2,3,4` → 5, 13, 33, 81, taken off
  `universalCircuit_size` rather than off `universalCircuit_const_true_size`.
- Mandated `awk`, verbatim:

  ```
  total=179 code=76 comment=83 blank=20
  ```

- **No Lean changed**, verified independently: `set_option maxHeartbeats`→EOF from `HEAD`
  and the working tree, **108 lines each, `diff` empty**. `HEAD` is still the round-1 commit,
  so this holds across all three rounds — `code=76` has not moved once.

### "The growth was all exempt" — checked, and it is true

The convenient claim, verified by reading the spans off the file rather than accepting them:

| span | round 2 | round 3 |
|---|---|---|
| docstring | 10–68 = 59 | 10–70 = **61** |
| `## Divergences` (exempt) | 32–54 = 23 | 32–56 = **25** |
| `## Implementation notes` (non-exempt) | 56–62 = 7 | 58–64 = **7** |
| `## References` (exempt) | 64–67 = 4 | 66–69 = **4** |
| non-exempt | 32 | **32** |
| comment after exemption | 54 | **54** |

`total` +2, `comment` +2, `code` +0, `blank` +0, and the Divergences span +2 with every other
span unchanged — so the two added lines are inside the exempt block and nowhere else. Both
non-exempt figures are genuinely unchanged, 32 against the ~40 cap and 54 against `code=76`.

### The `¬` hedge — applied correctly, and the caveat landed on the right term

`:43` now reads "`n` shared `¬` gates" — "at most" gone. `:44–46` carries the caveat, on the
`∨` term where I said it belonged.

Both of the unit's justifications verified against the PDF:

- **The `pp.107–108` citation is exactly right, and a single-page cite would have been
  wrong.** PDF p.134 (book 108) *begins* with "of f − 1 gates of fan-in 2." The sentence
  starts on book p.107 — "a ∨ or ∧ gate with fan-in f can be easily repaced with a subcircuit
  consisting" — and completes on 108. It straddles, as reported.
- **The exactly-`n` reading is right.** Note first that `pdftotext` renders p. 46's example as
  "z1 ∨ z2 ∨ z3 ∨ z4" in every mode — AB's overbars are drawn rules, not characters, so text
  extraction silently drops them. A critic working from extraction alone could conclude the
  unit invented the bars. It did not: the bars are *forced* by the surrounding text, which
  extraction does preserve — "there exists a clause `C_v(z₁,…,z_ℓ)` such that **`C_v(v) = 0`**
  and `C_v(u) = 1` for every `u ≠ v`". A disjunction vanishing at `v` needs every literal
  false at `v`, so literal `i` is `z̄ᵢ` exactly when `vᵢ = 1`, giving `z̄₁ ∨ z̄₂ ∨ z₃ ∨ z̄₄` for
  `v = 1,1,0,1`. AB states the overbar convention outright on p. 44 ("`ūᵢ` denotes `¬uᵢ`"),
  which extraction *does* preserve. With all `2ⁿ` clauses present, every `i` has some `v` with
  `vᵢ = 1`, so every `z̄ᵢ` occurs; and a `¬` gate has fan-in 1 so it cannot serve two
  variables, while Def 6.1 bounds no fan-out so one per variable suffices. Exactly `n`, both
  directions.

### Ruling on the prefix-sharing figure: the caveat is strong enough as written; do not import it

Asked for, so ruled on squarely. **The qualitative form is sufficient and the quantitative
form would be a defect.**

The caveat's whole job is to stop `n·2ⁿ + 2n - 1` being read as *the* Def 6.1 cost of this
function rather than the cost of AB's own construction. "not a lower bound on what a DAG
needs" discharges that completely — it is the entire logical content of the risk, and a
downstream reader who takes only that away cannot go wrong.

My `≈3·2ⁿ` does check out (prefix-share the clause `∨`-trees: distinct internal OR nodes
`Σ_{k=2}^{n} 2ᵏ = 2ⁿ⁺¹ − 4`, plus `2ⁿ−1` `∧`, plus `n` sources and `n` `¬`). But correctness
is not the test. Three reasons it stays out:

1. **It is not derived in the file.** That is the exact ground on which the unit kept it out,
   and it is the ground on which I kept my own `2n·2ⁿ` counterfactual out in round 2. The
   standard has to run both ways or it is not a standard. The unit applied it to me correctly.
2. **No consumer needs it.** U11 needs the bound and the fact that the constant is ours. It
   does not need to know how loose AB is.
3. **It is scope creep, and the worse kind.** `Universal.lean` exists to explain its own
   constant against AB's quoted figure, not to improve on AB. The observation is really
   "AB's `n2ⁿ` is loose by a factor of `~n` under his own Def 6.1 once you share" — a claim
   about the book, unproved here and unprovable here without a Def 6.1 circuit type TCSlib
   does not have. Sixteen rounds of Blocking findings have all been prose asserting more than
   the code does; this would have been the seventeenth.

No change. The caveat stands.

### Round 2's Blocking — `ch6/NOT_FORMALIZED.md:27` — FIXED, and fixed the right way

The row no longer carries a number. What remains is qualitative and all of it is true:
`Circuit.size` is a tree charging for every literal occurrence and reusing nothing (`Basic.lean:157–159`);
it charges `1` for a `k`-ary gate where Def 6.1 charges `k−1` vertices (AB pp.107–108). Then it
points at `Universal.lean`'s `## Divergences` "do not restate it here", and names the
unformalized part per the `PARTIAL` legend at `:7`.

This is the right repair rather than a third attempt at the arithmetic, and the diagnosis
recorded with it is accurate: round 1 collapsed AB's two conventions, round 2 the two
baselines, the docstring was correct both times.

### The two new standing rules — both well-founded, and the second one nearly bit me

`ch6/REVIEW_CRITERIA.md:110–117` ("Summaries cite, they do not re-derive") generalizes
correctly from the two failures and states the right diagnostic: *if a summary needs an
equation to make its point, the point belongs in the file.* Both failures are recorded as the
reason, which is what stops it being re-litigated.

`:119–124` (unit-numbered scratch files) is not hypothetical. Listing the shared scratch root
shows `u10_axcheck.lean`, `u10r2_check.lean`, `u12_axioms.lean` alongside mine, plus a large
population of generic names from earlier units — `Axioms.lean`, `Ax2.lean`, `Check2.lean`,
`B1.lean`, `ax.out`, `full.log`. **It is one directory, shared, not per-session.** My own
round-1 build figures were read back from files I had named `b_universal.log`, `b_agg.log`
and `b_full.log` — as collision-prone as anything on that list. Those conclusions stand only
because rounds 2 and 3 re-ran every one of them under `u9r2_*` / `u9r3_*` names and read the
module and aggregator builds inline rather than through a file, and the figures came out
internally consistent and monotone (916 stable; aggregator 3043 → 3044 → 3045 as
`HardFunctions` and `NCAC` were registered; full 3697 → 3698 → 3699). I could not have proved
the round-1 files unclobbered after the fact, which is the rule's point. My unnumbered
leftovers are deleted.

### Advisory

- [Advisory] `ch6/NOT_FORMALIZED.md:27` — "the full accounting ... is in `Universal.lean`'s
  `## Divergences` block, **which is proved and checked**". The tree-side number is proved
  (`universalCircuit_size_le`, `universalCircuit_const_true_size`); the two AB-side counts,
  `n·2ⁿ − 1` symbols and `n·2ⁿ + 2n − 1` vertices, are *checked against the book* but are not
  theorems in this repository and cannot be until a Def 6.1 circuit type exists. "Proved"
  invites a later reader to cite them as TCSlib results. → "checked against the book", or
  just "checked". One word; does not hold up the unit, and the row is otherwise the best
  version of itself in three rounds.

### Verdict

**PASS** — zero Blocking. Round 2's Blocking is fixed at the source rather than patched, the
`¬` Advisory is applied with both of its textual justifications independently confirmed
against the PDF, the measurements all reproduce including the one flagged as convenient, and
no Lean has changed since round 1 — `code=76`, 11 public declarations `sorry`-free, the bound
exact and attained.

Closing note on the unit, since this is its last round. The mathematics was right in round 1
and was never touched again; all three rounds were spent on prose. The file ends up saying
something true and non-obvious that AB does not say — that `n2ⁿ` survives both of AB's own
conventions, and that our excess over it is `2ⁿ + 2` because our literal leaves happen to come
to within one of AB's whole symbol count while our gate nodes are charged and his are not.
That is a better artifact than the round-1 version, which had the same theorem and a wrong
reason for its constant. The residue is where the defects migrated: two of the three Blocking
findings across the unit's life were in the ledger rows summarising the file, not the file,
and `REVIEW_CRITERIA.md:110–117` now exists to stop that recurring.

U9 → `DONE`. `Universal.lean` needs nothing further; `NOT_FORMALIZED.md:27`'s one word is
orchestrator-owned and does not gate the flip.

---

## U12 — round 1 — REVISE

**The mathematics is sound and nothing in the Lean is wrong.** All four `toBinary` lemmas,
the `inNC_succ` chain, the `PARITY` dual-pair construction and the `+ 1` in `HasLogDepth`
check out, by hand and by Lean. Every Blocking finding below is again prose asserting more
or other than the code does — the sixth consecutive round in which that is the whole of the
Blocking set — plus one policy §1 violation the unit correctly identified and could not
itself repair.

### Independently verified, not accepted on report

Every figure re-measured under unit-numbered scratch names; no file I did not write myself
was read back.

- `lake build TCSlib.Complexity.CircuitComplexity` — **3045 jobs, exit 0** ✓ matches the
  post-registration figure. (The unit's own 907 predates registration.)
- `lake build` (full) — **3699 jobs, exit 0**. The unit reported 3698; the extra job is
  `NCAC` itself entering the reachable set when it was added to the aggregator, so 3698 was
  a pre-registration measurement and is consistent, not wrong.
- `zsh scripts/lean_check.sh TCSlib/Complexity/CircuitComplexity/NCAC.lean` — no output,
  rc 0.
- `grep -n "sorry\|admit\|native_decide"` — empty.
- **Axiom sweep re-done from scratch**, not trusted from a deleted scan block. A scratch
  file `u12_axioms.lean` imports the module and walks `env.constants` filtered by
  `env.getModuleIdxFor? = getModuleIdx? \`TCSlib.Complexity.CircuitComplexity.NCAC`,
  calling `Lean.collectAxioms` on each. Output:
  `declarations scanned: 64` / `axioms used (union): [Quot.sound, Classical.choice, propext]`
  / `sorryAx users: []`. **64 confirmed, no `sorryAx`.** (Filtering by module index rather
  than `map₂` is the reproducible form; `map₂` only works from inside the file itself, which
  is why the unit's method left nothing behind to re-run.)
- Every declaration carries a docstring (the one apparent miss, `mem_language_iff:97`, has
  its docstring above an intervening `@[simp]`).
- Mandated `awk`, verbatim:

  ```
  total=1000 code=682 comment=193 blank=125
  ```

  ✓ matches exactly. `comment=193 < code=682`, so item 7's ratio is met. Module docstring is
  `11–66` = 56 lines; `## Divergences` `35–61` = 27; `## References` `62–65` = 4; non-exempt
  = **25**, against the ~40 cap. The unit's "24" is the same span without the closing `-/`.
  No item 7 finding.

### The mathematics — checked line by line

`toBinary`. `combine b cs = combineFuel b cs.length cs`, and `cs.length` is enough fuel: the
fuel-exhaustion branch `combineFuel b 0 cs = Circuit.node b cs` is reachable only with
`cs = []`, since every lemma about it carries `cs.length ≤ k`. The four properties:
`toBinary_eval:461` ✓; `toBinary_maxFanin_le:472` ✓ (`max 2 2 = 2` at the node, `0 ≤ 2` at a
leaf); `toBinary_size_le:507` ✓ via `toBinary_size_succ_le`'s strengthened
`|toBinary c| + 1 ≤ 3|c|`, where the node case has exactly the two units of slack the
`+ 1` buys (`3·sumSize + 2 ≤ 3·(1 + sumSize)`); `toBinary_depth_le:511` ✓, with
`(1 + maxDepth) * (clog w + 1)` matching `combine_depth`'s
`maxDepth·(clog w + 1) + clog w + 1` on the nose.

`inNC_succ:556`. `maxFanin ≤ size ≤ a(n+1)^k` ✓. `clog_poly_le:533` is right —
`a < 2^a` and `m + 1 ≤ 2^(log₂ m + 1)` give `a(m+1)^k ≤ 2^(a + k(log₂ m + 1))` ✓ — and the
step to `clog₂(a(n+1)^k) + 1 ≤ (a+k+1)(log₂ n + 1)` uses `a ≤ a(log₂ n + 1)` and
`1 ≤ log₂ n + 1` ✓. Resulting witnesses `(3a, k)` for size and `b(a+k+1)` for depth ✓.

`PARITY`. The dual-pair invariant holds and is maintained: `xorNode:655` builds
`(a∧b')∨(a'∧b)` and `(a∧b)∨(a'∧b')`, which under `b' = ¬b`, `a' = ¬a` are `a⊕b` and
`¬(a⊕b)` ✓, at two levels ✓; `xorFuel`'s base pair `(node false [], node true [])` is
`(false, true)`, dual ✓, and agrees with `xorAll x [] = false` ✓; `isDual_xorPairUp` carries
it up the tree ✓. Depth `2·clog₂ n + 2 ≤ 2(log₂ n + 1) + 2 ≤ 4(log₂ n + 1)` ✓.

**The `w`-vs-reindexing bridge is real.** `parity_inNC_one:994` closes with
`← List.foldr_map` then `List.finRange_map_get`, i.e.
`(List.finRange w.length).map w.get = w`, so the fold really is over `w`'s own letters in
order, not over a permuted index set. `Accepts` feeds the circuit `w.get` at length
`w.length`, and `Language.parity:967` is `{w | w.count true % 2 = 1}`, AB Ex 6.26's wording
verbatim. ✓

**The `+ 1` in `HasLogDepth:112` is load-bearing, exactly as claimed.** `parityPairs 0 = []`,
so `xorTree [] = xorFuel 0 []= (Circuit.node false [], _)` and `parityCircuit 0` has
`depth = 1 + maxDepth [] = 1`. `Nat.log 2 0 = Nat.log 2 1 = 0`, so
`b * (Nat.log 2 n) ^ 1 = 0` would demand depth `0` at `n ∈ {0,1}` and `parity_inNC_one`
would be false. Confirmed. `parityCircuit_eval_zero` / `_eval_one` pin both edge cases. ✓

**Unions match AB.** `NC = ⋃ i ∈ Set.Ici 1, NCLevel i` (`:137`) against Def 6.24's
`∪_{i≥1} NC^i`, and `AC = ⋃ i, ACLevel i` (`:140`) against Def 6.25's `∪_{i≥0} AC^i` ✓,
read off PDF pp. 117–118. `HasFaninTwo` is faithful: Def 6.24 inherits fan-in 2 from Def 6.1
and Def 6.25 is the definition that relaxes it. ✓

### Blocking

- [Blocking] `TCSlib/Complexity/CircuitComplexity/NCAC.lean:39-41` — "`NC¹` is unaffected —
  a fan-in-2 tree of depth `O(log n)` has `poly(n)` nodes, and conversely". Two defects in
  one clause. (a) The literal converse of the sentence just made is "a fan-in-2 tree with
  `poly(n)` nodes has depth `O(log n)`", which is **false**: the right comb
  `node [lit, node [lit, node [...]]]` has `2n+1` nodes and depth `n`. (b) On the intended
  reading — that an AB fan-in-2 **DAG** of depth `O(log n)` unfolds into a tree of the same
  depth and hence `poly(n)` nodes — "`NC¹` is unaffected" asserts **equality** of
  `Language.InNC 1` with AB's DAG `NC¹`. AB's DAG classes are defined nowhere in this repo
  and the unfolding is not formalized, so this is an unproved class-preservation claim in
  the one place the divergence is said to vanish. `Circuit.size_succ_le_two_pow:624` is a
  statement about trees only and supplies neither half of it. → State the formalized fact
  and mark the rest as informal: "`Language.InNC 1` is AB's `NC¹` restricted to fan-out 1.
  The restriction is expected to be harmless at `i = 1`, since unfolding a fan-in-2 DAG of
  depth `d` into a tree costs at most `2 ^ (d+1)` nodes, which is `poly(n)` at
  `d = O(log n)`; **neither AB's DAG classes nor that unfolding is formalized here, so this
  is not a theorem of this development.** `Circuit.size_succ_le_two_pow` proves only the
  tree-side bound."

- [Blocking] `TCSlib/Complexity/CircuitComplexity/NCAC.lean:45-46` — "Consequently
  `NC ⊆ P/poly` is **not statable**: the two classes are over different circuit types."
  False. `BoolCircuit.NC : Set (Language Bool)` (`:137`) and `ACP.PPoly : Set (Language Bool)`
  (`PPoly.lean:131`) are both sets of `Language Bool`; `BoolCircuit.NC ⊆ ACP.PPoly`
  typechecks as written. What is absent is a **bridge** from `BoolCircuit.Circuit` to
  `ACP.CircuitFamily` with which to *prove* it — a gap `ch6/PLAN.md` already carries under
  "Deferred follow-ups". → "`NC ⊆ P/poly` is stated over two circuit types and is therefore
  not provable here: no bridge from `BoolCircuit.Circuit` to `ACP.CircuitFamily` exists
  (`ch6/PLAN.md`, deferred follow-ups)."

- [Blocking] `TCSlib/Complexity/CircuitComplexity/NCAC.lean:39-41` — the `## Divergences`
  block records the fan-out-1 preservation boundary for `NC` only, and is silent on `AC`,
  although the file defines `Language.InAC:124`, `AC:140` and proves `AC^i ⊆ NC^{i+1}`. The
  boundary is not the same on the two sides: unfolding a depth-`D`, size-`S` DAG costs
  `S^D`, so it is `AC⁰` — constant depth — that survives on the `AC` side, whereas on the
  `NC` side it is `NC¹`. A reader is left to carry the "`i ≥ 2`" caveat across to `AC`,
  where it is wrong by one level. This is structurally the same defect as the recurring
  one: a prose account that names the boundary on one side and omits the other. → Add the
  `AC` half explicitly, or state the caveat once in a form that names both indices.

- [Blocking] `TCSlib/Complexity/CircuitComplexity/NCAC.lean:35-61` — the `## Divergences`
  block records **no size-measure divergence**, though `IsPolySize:102` is AB's "poly(n)
  size" condition measured by `Circuit.size`, which diverges from Def 6.1 (p. 107) in both
  directions: it charges **1** for a `k`-ary gate where AB charges `k − 1` vertices
  (lowering our count), and it pays for **every literal occurrence** with no shared source
  and no gate reuse (raising it). This is precisely the pair of effects `ch6/NOT_FORMALIZED.md`
  had to be corrected twice to state symmetrically, and it matters more here than in U9/U10:
  `AC^i` is the unbounded-fan-in class, so the `k`-vs-`k−1` term is unbounded, not a
  constant. Rubric item 2 names `PPoly.lean`'s record as the model, and `PPoly.lean:38-47`
  does carry it ("AB counts input vertices in `|C|` and allows arbitrary DAGs; we count
  non-input nodes…, costing `+n` and a factor `≤ s`"); `Basic.lean:45-50` records a size
  divergence against [OD14] only, not against AB. → Add one bullet naming **both**
  directions. Do not name only the ones that raise our count.

- [Blocking] `policy.md` §1 vs `TCSlib/Complexity/CircuitComplexity/NCAC.lean:1000` —
  **1000 lines**, measured, against a 150–600 target and an explicit "a file approaching
  1000 lines should be split unless there is a positive reason not to (e.g. a single long
  proof that cannot be usefully decomposed)". The exception does not apply: there is no
  single long proof here, and the file already carries its own split point at `:610`
  (`/-! ### Size from depth, and PARITY -/`). File ownership is a process constraint, not a
  positive reason under §1. The split, authorised:
  - **Keep in `NCAC.lean`** (`1–604`): families, `InNC`/`InAC`, `NCLevel`/`ACLevel`/`NC`/`AC`,
    `InNC.inAC`, `pairUp`/`combine*`/`toBinary` and its four lemmas, `clog_poly_le`,
    `InAC.inNC_succ`, the two level inclusions, `NC_eq_AC`.
  - **Move to a new `CircuitComplexity/Parity.lean`** (`606–1000`, ~395 lines):
    `xorNode`…`parityCircuit*`, `Language.parity`, `mem_parity_iff`, `parity_inNC_one`.
  - **Move to `Basic.lean`** the shared plumbing both halves need, which is also what
    `policy.md` §1 *Helpers* requires: the `### Structural unfoldings` block `161–238`
    (`maxFaninL` promoted to a public `Circuit.maxFaninL`, `depth_node`, `size_node`,
    `maxFanin_node`, the six `_nil`/`_cons` lemmas, `depth_le_maxDepth`,
    `maxFanin_le_maxFaninL`, `length_le_sumSize`, `maxFaninL_le_sumSize`),
    `Circuit.maxFanin_le_size:240`, and `sumSize_add_length_le:613` +
    `Circuit.size_succ_le_two_pow:624`.

    That lands `NCAC.lean` ≈ 515, `Parity.lean` ≈ 350, both inside the 150–600 target,
    and it discharges the unit's own "these two belong in `Basic.lean`" report in the same
    move. The aggregator import list and `ch6/PLAN.md` are orchestrator-owned; the new file
    must be registered in `TCSlib/Complexity/CircuitComplexity.lean` or CI will not see it.

### Advisory

- [Advisory] `NCAC.lean:595` — `NC_eq_AC` is tagged `[AB09, p. 118]`, but p. 118 states only
  `NC^i ⊆ AC^i ⊆ NC^{i+1}`; AB never writes `NC = AC`. → "corollary of [AB09, p. 118]".
- [Advisory] `NCAC.lean:783-787` — `xorFuel`'s zero-fuel branch returns the constant-`false`
  pair for *any* `ps`, which is semantically wrong when `ps ≠ []`. Unreachable, because every
  lemma and `xorTree` itself carry `ps.length ≤ k` — but `combineFuel`'s corresponding branch
  returns the mathematically correct `Circuit.node b cs`, and the asymmetry is a trap for a
  later reader. → Return `(Circuit.node false (ps.map Prod.fst), Circuit.node true …)`, or
  note in the docstring that the branch is unreachable.
- [Advisory] `NCAC.lean:28-30` and `:624` — the `2 ^ (d+1)` bound is stated in both the
  module docstring and the declaration docstring. Item 7 wants it once.

### Rulings the orchestrator asked for

**Fan-out-1 divergence — acceptable as a model, rejected as written.** "AB's classes
restricted to formulas, recorded as a divergence" is the right call and I would not ask for
`FeedForward`: `NC^i ⊆ AC^i ⊆ NC^{i+1}` and `NC = AC` are genuine theorems of the formalized
model, the model is internally coherent, and the stated reason for rejecting `FeedForward`
(`toBinary` recurses over a gate's child list, which a layered DAG does not have) is
correct and specific. The unit does not overclaim on the theorems. What fails is the
divergence block's three claims *about AB's classes* — the `i = 1` equality, the false
converse, and "not statable" — which are the Blocking items above. Fix the prose; keep the
model. The `## Divergences` block should claim only (i) what the formalized classes are,
(ii) that they are AB's with fan-out 1, and (iii) explicitly-flagged informal expectations
about the relationship, never stated as fact.

**Namespace — `BoolCircuit` is right, and it should bind.** `policy.md` §1 *Namespaces* asks
for one root per topic used consistently; the topic here is `BoolCircuit.Circuit`, whose root
is `BoolCircuit` (`Basic.lean:70`), and `CircuitSat.lean:59` already does the same.
`Circuit.maxFanin_le_size` could not live under `ACP` without ceasing to resolve into its
type's namespace, and `ACP.CircuitFamily` already occupies the name
`TreeCircuitFamily` would have wanted. `ch6/PLAN.md`'s "circuit machinery goes in `ACP`"
predates the two-circuit-type split and should be amended to **namespace follows the circuit
type** — `ACP` for `FeedForward`, `BoolCircuit` for `Circuit`, `Language` for language-level
notions. Under that rule `ACP.cktSatLang` (`Encoding.lean:286`) is misplaced: it is a
language *of `BoolCircuit.Circuit`s*. That is a cross-track move against a `DONE` file and
belongs to the cross-cutting pass, not to U12.

**Constants — clean.** `toBinary_size_le`'s 3 (`:507`), `parityCircuit_size_le`'s
`32(n+1)^4` (`:937`) and `parityCircuit_depth_le`'s 4 (`:925`) are each documented as what
they are ("at most triples the size", "depth `O(log n)`", "polynomial size"), and none is
attributed to AB or called optimal. AB gives no constants at any of the three points, so
`policy.md` §2's deviation clause has nothing to bite on, and explicit `∀`-bounds are what
Advisory item 7 asks for.

**`Circuit.one_le_size` — no duplicate, verified.** The only declaration is
`_root_.BoolCircuit.Circuit.one_le_size` at
`TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean:105`. `NCAC.lean` does not
redeclare it; it inlines `have hc : 1 ≤ c.size := by cases c <;> simp [Circuit.size]` at
`:223`, which it must, since it does not import that file. Correct call. Hoisting the
`_root_` lemma into `Basic.lean` is queued with the split above, and the inline `have` then
collapses. `maxFanin_le_size` and `size_succ_le_two_pow` appear nowhere else in `TCSlib/`.

### Ledger rows — the wording I will accept

Both belong under "§§6.3–6.8, pp. 113–122". Neither re-derives anything, per
`REVIEW_CRITERIA.md:110-117`; both point at the module docstring for the content.

Row 1, in the blocked table:

```
| **`NC⁰ ⊊ AC⁰`** (p. 118) and **`PARITY ∉ AC⁰`** (Ex 6.26) | BLOCKED | Forward references
to Chapter 14, outside this range; AB states and proves neither here. The library's one
constant-depth lower bound, `MODq_notin_AC0p_quantitative`
(`TCSlib/BooleanAnalysis/RazborovSmolensky.lean:1203`), is a different statement over a
different circuit type and does not discharge either. |
```

Row 2, as its own PARTIAL row:

```
| **Defs 6.24 / 6.25 over AB's circuits** | PARTIAL | `NCAC.lean` formalizes `NC^d`, `AC^d`,
`NC`, `AC`, `NC^i ⊆ AC^i ⊆ NC^{i+1}` and `PARITY ∈ NC¹` over `BoolCircuit.Circuit`, which is
a tree — so every class there is AB's with fan-out restricted to 1 (formulas), where Def 6.1
circuits are DAGs. **Not formalized:** AB's DAG classes, and hence any comparison between
them and these. `NCAC.lean`'s `## Divergences` says which levels the restriction is and is
not expected to preserve, and flags those expectations as informal. |
```

Do not add Row 2 until the `## Divergences` block actually flags them as informal — as the
file stands today, the row would point at prose that asserts the `i = 1` case as fact.

### Verdict

**REVISE** — five Blocking. No Lean needs to change: four of the five are the module
docstring, and the fifth is a file split plus two hoists into `Basic.lean` that move
declarations without touching a tactic. The unit's own self-assessment was accurate on every
count it could act on — it identified the file-size violation, the correct split, the two
misplaced general lemmas and the `one_le_size` duplication risk, and its four measurements
all reproduce. The defects are where they have been for six rounds: in the sentences that
describe the gap between this model and Arora–Barak's, and this time in both of the shapes
the log has seen — an unproved class-preservation claim, and a size account that names some
effects and not the others.

---

## U12 — round 2 — REVISE

**Four of the five round-1 Blocking are fixed cleanly, and all three Advisories are
applied. The split is exactly as specified and the mathematics is untouched.** One Blocking
remains, and it is in the same bullet as round 1's Blocking 1: the sentence rewritten to fix
it acquired a false quantitative claim doing so. This is the U9 round-2 pattern, and it is
ruled the same way. One clause; nothing else stands between U12 and `DONE`.

### "No tactic changed" — verified structurally, and the claim needs one correction

`HEAD` is **not** the round-1 state (`HEAD:NCAC.lean` is 862 lines, an earlier draft), so
there is no git baseline for round 1 and I did not pretend to one. What I checked instead:

**Declaration inventory, exhaustive.** Every declaration I verified in round 1 is present,
in the same order, with nothing added and nothing dropped: 49 in `NCAC.lean`, 39 in
`Parity.lean`, 18 in `Basic.lean`'s new Section 2b. The round-1 file's 106 declarations
partition across the three with no remainder.

**Body-level diff against the round-1 text.** `Basic.lean`'s new block is a full `git diff`
and I read it line for line; `NCAC.lean`'s `combine`/`toBinary` region and `Parity.lean` I
compared against the round-1 bytes. The complete set of differences:

1. **The predicted collapse**, `length_le_sumSize`: `have hc : 1 ≤ c.size := by cases c <;>
   simp [Circuit.size]` → `have hc := Circuit.one_le_size c`. Exactly as forecast.
2. **`maxFaninL` → `Circuit.maxFaninL`**, forced by the promotion out of `private`. In
   statements: `NCAC.lean:231,268,331,375,443` and five lines in `Basic.lean`. **And in
   three tactic lines** — `Basic.lean`'s `maxFanin_node` proof (`simp [Circuit.maxFanin,
   maxFaninL]` → `simp [Circuit.maxFanin, Circuit.maxFaninL]`) and the `hfan` type
   ascriptions inside `size_succ_le_two_pow` and `toBinary_depth_le`. **So "no tactic
   changed anywhere" is overstated by three lines.** All three are pure requalification of
   one name; none is a mathematical change; the claim's substance holds. Every lemma *name*
   used inside a proof (`maxFaninL_cons`, `maxFaninL_nil`, `maxFanin_le_maxFaninL`) is
   untouched, because those live in `BoolCircuit` and only the *definition* moved into
   `Circuit`.
3. **`private` dropped** from the twelve unfoldings and from `maxFaninL`; `sumSize_add_length_le`
   correctly stays `private` (its only user is in the same file).
4. **`one_le_size` alpha-renamed** `C` → `c` on the hoist. `Basic.lean`'s Provenance note
   says "unchanged"; that is true up to the binder name.

No other line differs. The mathematics verified in round 1 carries over in full, and I did
not re-derive it.

### Measurements — re-run, unit-numbered scratch

- `lake build TCSlib.Complexity.CircuitComplexity` — **3046 jobs, exit 0** ✓ matches.
- `lake build` (full) — **3700 jobs, exit 0**, not the 3699 reported. The extra job is
  `Parity.lean` entering the reachable set on registration, the same off-by-one as round 1's
  3698→3699. **3699 was measured before registering `Parity`.** Third round in this loop
  where a build figure was quoted across a registration; worth a habit, not a finding.
- `zsh scripts/lean_check.sh` on all four touched files — no output, `rc=0` each ✓.
- `grep -n "sorry\|admit\|native_decide"` across the three — empty ✓.
- Mandated `awk`, verbatim, all three ✓ match exactly:

  ```
  Basic   total=675 code=380 comment=215 blank=80
  NCAC    total=528 code=329 comment=135 blank=64
  Parity  total=404 code=265 comment=95 blank=44
  ```

  Comment under code in all three.
- Non-exempt docstrings, spans read off the files: `NCAC` `11–77`=67, Div `34–72`=39,
  Ref `73–76`=4 → **24**; `Parity` `10–47`=38, Div `26–42`=17, Ref `43–46`=4 → **17**;
  `Basic` `18–73`=56, Div `47–57`=11, Ref `69–72`=4 → **41**. The unit's 23 and 16 are the
  same spans without the closing `-/`; the convention difference is one line and does not
  matter at these margins. `Basic`'s 41 is the one at the cap — see Advisory.
- Proof sketches survive verbatim on `InAC.inNC_succ` and `parity_inNC_one` ✓, as
  `policy.md` §3 requires.
- No residual claim anywhere in `TCSlib/`: `grep -rn "unaffected\|not statable\|and
  conversely"` returns only this log's own history.

### The axiom sweep — 610 confirmed, with a correction to what it counts

Re-run myself (`u12r2_axioms.lean`, module-index filter, **no** `isInternal` guard,
`collectAxioms` on every constant):

```
Basic:  total=374 (internal/mangled=146)  axioms=[Quot.sound, Classical.choice, propext]  sorryAx=[]
NCAC:   total=139 (internal/mangled=94)   axioms=[Quot.sound, Classical.choice, propext]  sorryAx=[]
Parity: total=97  (internal/mangled=86)   axioms=[Quot.sound, Classical.choice, propext]  sorryAx=[]
```

**610 confirmed exactly**, no `sorryAx`, nothing outside the three standard axioms.

**The method is right and I endorse it. The framing needs two corrections**, and since it
is now in the rubric they matter more than they would in a report:

- **610 are not 610 declarations.** 326 of them are internal or mangled — `private`
  declarations, equation lemmas, `match_*`/`proof_*` terms, recursors. Non-internal is
  **284**. The honest label is "constants attributed to the module".
- **64 vs 610 is not the guard's effect.** Round 1's 64 was the *public* declaration count
  of **one** 1000-line file; 610 is *all* constants of **three** files, one of which
  (`Basic.lean`, 374) is mostly pre-existing content U12 never touched. Comparable figures
  are round 1's 64 against round 2's ~74 public declarations over the same material.
- **The guard was a narrow gap, not a hole.** `collectAxioms` is transitive, so a `sorryAx`
  inside a `private` lemma reachable from *any* public declaration was already caught in
  round 1. Only a private declaration used by nothing public could have hidden one — dead
  code. Worth closing, and now closed; worth saying so, so a future unit does not read the
  rubric as "every previous sweep was worthless".

### Blocking

- [Blocking] `TCSlib/Complexity/CircuitComplexity/NCAC.lean:43` — "Unfolding a fan-in-`f`
  DAG of depth `d` into a tree … **costs at most `f ^ d` nodes**". False as written. A
  depth-`d`, fan-in-`f` tree has `f ^ d` nodes *in its bottom level*; its total node count
  is `(f^(d+1) − 1)/(f − 1)`, which at `f = 2` is `2^(d+1) − 1` — the very bound
  `Circuit.size_succ_le_two_pow` proves two lines below. Worse, the quantity the argument
  needs is not a node count at all: unfolding a **size-`S`** DAG gives a tree of at most
  `S · f ^ d` nodes, and it is that product staying polynomial — poly × poly — that carries
  "expected to be harmless". As written the sentence states a false count and omits the `S`
  it depends on, while the following clause ("where *that* stays polynomial") silently
  reinterprets `f ^ d` as the blow-up factor, which is the reading under which it *is*
  correct. That ambiguity between a true reading and a false one is the same defect as
  round 1's "and conversely", in the same bullet, one revision later. → "**duplicates a node
  once per consumer, blowing the node count up by a factor of at most `f ^ d`**, so the
  fan-out-1 restriction is expected to be harmless exactly where a polynomial-size family
  stays polynomial: …". One clause; nothing else in the block needs touching.

  Dropping the `2 ^ (d+1)` numeral for a general `f` was otherwise the **right** call, and
  I endorse both reasons given: the bullet now has to cover `f = 2` and `f = poly(n)`, and
  Advisory 3 did forbid restating the bound outside its declaration. The generalisation is
  correct; only its arithmetic is wrong.

### Round-1 Blocking — dispositions

- **B1 (the `i = 1` equality).** Fixed at the source. "What is formalized" (`:36-41`) now
  states that AB's DAG classes are defined nowhere here and that **no comparison is
  formalized**, and hands off to the next bullet explicitly as "not a theorem of anything
  below"; the expectation bullet closes "**neither expectation is a theorem of this
  development**" and correctly narrows `Circuit.size_succ_le_two_pow` to "only the
  tree-side bound". The false "and conversely" is gone. `Parity.lean:38-41` carries the
  same qualification rather than restating the argument. Nothing in either file asserts
  the equality. **Dropped** — the residue is the arithmetic above, not the claim.
- **B2 (`NC ⊆ P/poly` "not statable").** Fixed exactly (`:67-69`): "Statable — both are
  `Set (Language Bool)` — but not provable here", with the missing bridge and the
  `ch6/PLAN.md` pointer. **Dropped.**
- **B3 (the `AC` boundary).** Fixed, and the parameters check out: `NC` at `i = 1` is
  `f = 2`, `d = O(log n)` ✓; `AC` at `i = 0` is `f = poly(n)`, `d = O(1)` ✓; and "the two
  indices differ, so the `NC` boundary must not be carried across to `AC`" is the point,
  stated. **Dropped.**
- **B4 (size measure).** Fixed and correct in both directions (`:50-55`): *lowers* by
  charging `1` for a `k`-ary gate against Def 6.1's `k − 1` — with the "unbounded here, not
  a constant, since `AC^i` is the unbounded-fan-in class" point — and by not carrying AB's
  `n` input vertices; *raises* by charging every literal occurrence a leaf, no shared
  sources, no gate reuse. The downward effect is named **first**. The new **Basis** bullet
  (`:62-63`) is a real divergence I had not asked for and is right: Def 6.1 counts `¬`
  vertices, `Circuit` negates at literals for free. **Dropped.**
- **B5 (file size).** Done as specified: `NCAC` 528, `Parity` 404, both inside the 150–600
  band, the shared plumbing in `Basic.lean`, `Parity.lean` registered, `PARITY` dropped from
  the `NCAC` bullet, and `Parity.lean` carries its own header, `set_option`s, four docstring
  sections, `[AB09, Ex 6.26]` tags and its own `## Divergences`. **Dropped.**

### Round-1 Advisories — dispositions

- **A1.** `NC_eq_AC:518` now reads "a corollary of [AB09, p. 118], which states the
  inclusions only". Applied.
- **A2. My advisory was wrong on the merits and the unit is right to have refused it.**
  `(Circuit.node false (ps.map Prod.fst), …)` is an OR over the first components, not their
  XOR — it would replace a visibly-inert placeholder with an expression a reader could
  mistake for the intended computation, which is worse for exactly the reader the advisory
  was protecting. Documenting the branch as unreachable (`Parity.lean:185-186`, naming that
  every lemma and `xorTree` supply `ps.length ≤ k`) is the correct disposal. **Withdrawn.**
- **A3.** The `2 ^ (d+1)` numeral now appears once, on `Circuit.size_succ_le_two_pow`'s own
  docstring; `Basic.lean`'s Main results describes it without the numeral. Applied.

### Advisory

- [Advisory] `TCSlib/Complexity/CircuitComplexity/Basic.lean` — 675 lines, over §1's 150–600
  band. **It stands.** §1 has two thresholds and this clears the one that triggers a split
  ("approaching 1000"); the growth is the direct and required consequence of §1's *Helpers*
  rule, and splitting the area's `Basic.lean` to keep it small would defeat the point of
  having one. Its non-exempt docstring is **41** lines against item 7's "under ~40" — inside
  the tilde, but with no margin left. If it grows again, the seam is already cut: Sections
  1–2b (`84–322`, types, `eval`, measures, arithmetic) against Sections 3–7 (`323–675`, the
  `NAndCircuit`/`NOrCircuit` normal form), ~240 and ~350. Trimming the three-line Provenance
  note to one would also buy back the docstring margin.
- [Advisory] `TCSlib/Complexity/CircuitComplexity/Basic.lean:195-249` — the twelve unfoldings
  sit at `BoolCircuit.depth_node`, `BoolCircuit.size_node`, `BoolCircuit.maxDepth_cons` and
  so on. Matching `toNAnd_eval` is a fair reading of item 11 and I do not overrule it, but
  the risk is concrete rather than stylistic: `NAndCircuit` and `NOrCircuit` are declared in
  the *same file* (`:333`, `:340`), each with its own `node` constructor, `size` and `depth`,
  and `FeedForwardCircuit.lean:101` does `open BoolCircuit`. The first `NAndCircuit`
  unfolding lemma anyone writes wants `size_node` and cannot have it. → Prefer
  `Circuit.depth_node` / `Circuit.size_node` / `Circuit.maxDepth_cons`, scoping them by the
  type they are about, as `Circuit.maxFaninL` already is. Cheap now, a rename later.
- [Advisory] `ch6/NOT_FORMALIZED.md:68` — the Chapter-14 row landed in the **`| AB item |
  Needs |`** table, whose preamble says "each is an `iff` or an implication with a class this
  library cannot define". `PARITY ∉ AC⁰` is neither, and the cell holds a reason, not a
  "Needs". → Move it to the three-column `| AB item | Status | Reason |` table at `:71`,
  where the fan-out row already sits, with status `BLOCKED`. The row's *content* is the
  wording I specified and is correct; only its placement is off.
- [Advisory] `ch6/NOT_FORMALIZED.md:75-77` — "**In scope and scheduled** … Claim 2.13 (U9),
  Theorem 6.21 (U10), Theorem 6.22 (U11), and Defs 6.24/6.25 … (U12)" is stale: U9 and U10
  are `DONE` and U12 is one clause away. Orchestrator-owned.
- [Advisory] `ch6/REVIEW_CRITERIA.md:126-128` — "One unit's sweep reported 64 declarations
  where the unguarded module-index sweep found 610 across the same three files" compares
  different things and will mislead the next unit. 64 was public declarations of one file;
  610 is all constants of three, 326 of them compiler-generated, and `Basic.lean`'s 374 are
  mostly pre-existing. → State the coverage rather than the ratio, and add that
  `collectAxioms` is transitive, so the guard could only ever have hidden a `sorryAx` in a
  `private` declaration reachable from nothing public.

### Verdict

**REVISE** — one Blocking, `NCAC.lean:43`. Everything else in this round is right, and most
of it is better than what I asked for: the `f`-general formulation, the Basis bullet, the
refusal of Advisory 2, and the decision to flag rather than hide `Basic.lean`'s 675 lines
are all improvements on my round-1 report, and two of them correct it.

The residue is worth naming, because it is now the unit's whole history. Round 1's Blocking
1 was a sentence true under one reading and false under another, in the bullet describing
the tree-vs-DAG gap. Round 2 rewrote that bullet, fixed the claim it was rejected for, and
produced a second sentence true under one reading and false under another, in the same
bullet, about the same gap. The mathematics has never been wrong and has never been touched;
what resists is saying, in prose, exactly how much smaller a formula is than a circuit.

## U11 — round 1 — REVISE

Two Blocking. Neither is a false theorem: the module builds, the axiom sweep is clean, and
every one of the nine theorems says what its name says. One Blocking is prose that states
the **opposite** of the hypothesis it describes; the other is a Mathlib lemma restated
verbatim. The framing — the thing this unit was most at risk on — is **sound, and is the
right call**; see the ruling below.

### Measurements

Mandated `awk` (`REVIEW_CRITERIA.md:66–75`), verbatim, on `Hierarchy.lean`:

```
total=333 code=151 comment=143 blank=39
```

`comment=143 < code=151` ✓. Module docstring is `:9–86` = 78 lines; exempt are
`## Divergences` `:38–74` (37) and `## References` `:82–85` (4), leaving **37 non-exempt**,
under the ~40 cap ✓.

| check | result |
|---|---|
| `lake build ...CircuitComplexity.Hierarchy` | **1032 jobs, exit 0** ✓ |
| `lake build TCSlib.Complexity.CircuitComplexity` | **3047 jobs, exit 0** ✓ (reproduces the figure in the brief) |
| `lake build` (full) | **3701 jobs, exit 0** ✓; only warning is the pre-existing `Rademacher.lean:552` unused-variable hit |
| `zsh scripts/lean_check.sh <file>` | no output, **exit 0** ✓ |
| `grep sorry` | empty ✓ |
| axiom sweep, module-index filter, **no `!nm.isInternal` guard** | **52 constants** in the module, **0** with any axiom outside `propext / Classical.choice / Quot.sound`. No `sorryAx`. |

The sweep matters here. The formalizer's own `u11_axioms.lean` enumerates **24**
`#print axioms` lines by hand and misses both `private` theorems (`foldr_congr`,
`eval_eq_of_iff`) along with 26 generated constants. The conclusion is the same, but a
hand-enumerated list is not the method `REVIEW_CRITERIA.md:119–125` asks for; re-run from
the module index.

### Blocking

- [Blocking] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:289–291 — **the two
  hypotheses are described backwards, and they are the whole point of AB's proof.**
  `treeSize_ssubset`'s docstring opens "With a padding length `ℓ` **short enough** that
  [AB09, Thm 6.21] bites at some length `n₀` and **long enough** that [AB09, Claim 2.13]
  still fits inside `T'`". Both clauses invert the code.
  `hlow : (ℓ n₀ + 4) * T n₀ < 2 ^ ℓ n₀` is satisfied by **large** `ℓ` — at `T n₀ = 1` it
  fails at `ℓ = 0,1,2` (`4<1`, `5<2`, `6<4`) and first holds at `ℓ = 3` (`7<8`), which is
  exactly why `treeSize_one_ssubset` takes `n₀ = 3`.
  `hup : 2 ^ ℓ n * (ℓ n + 1) + 1 ≤ T' n` is satisfied by **small** `ℓ` — at `T' n = 33` it
  holds at `ℓ = 3` (`33 ≤ 33`) and fails at `ℓ = 4` (`81 ≤ 33`).
  So `ℓ` must be long enough for 6.21 and short enough for 2.13 — AB's own tension, resolved
  on p.116 by `ℓ = 1.1 log n`. → Swap "short enough" and "long enough". The file's own
  `## Divergences` (`:63–65`) already gets the relationship right; this one sentence
  contradicts it.

- [Blocking] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:101–107 — `private theorem
  foldr_congr` is `List.foldr_ext` (`Mathlib/Data/List/Basic.lean:719`) restated verbatim,
  against Blocking item 4 ("anything else already in Mathlib. Search before defining").
  Verified available from `Hierarchy.lean`'s *exact* import set and a zero-glue drop-in:
  from `import ...HardFunctions` + `import ...Universal` alone,
  `example {α β} {f g : α → β → β} {init l} (h : ∀ a ∈ l, ∀ b, f a b = g a b) :
  l.foldr f init = l.foldr g init := List.foldr_ext f g init h` typechecks.
  → Delete `foldr_congr`; the four call sites (`:127`, `:136`, `:160`, `:169`) each become
  `List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc]`.

### Ruling on the framing — it stayed on the right side of the line

This is the question the brief flagged as highest-stakes, and the answer is that U11 did
what it was asked and did not shade it.

**Nothing is named `SIZE`, and nothing is named for 6.22.** `grep` confirms every occurrence of the
string `SIZE` in the file (`:13`, `:40`, `:41`, `:50`, `:51`) is inside a sentence saying
this is *not* that class, or naming what `Language.InSIZE` is instead. The nine theorem names are `widenCircuit_*`,
`restrictCircuit_*`, `padLanguage_*`, `treeSize_ssubset`, `treeSize_ssubset_of_lt`,
`treeSize_one_ssubset`, `zero_mem_treeSize_one` — not one invites 6.22.

**`InTreeSize` is far enough from `InSIZE`.** It carries the model in the name, it is a
different arity of thing from `ACP.PPoly`, and the definition (`:188–190`) quantifies over
`BoolCircuit.Circuit` with no gate-set field at all, where `Language.InSIZE`
(`PPoly.lean:109–111`) carries `OnlyUsesGates ACP.AC_GateOps` over `FeedForward (Fin 2)`.
A reader who opens the definition cannot confuse them.

**The three places a reader lands first all disclaim it, in that order.** Module docstring
line 3 (`:13–14`, before `## Main definitions`): "**It is not `Language.InSIZE`**, and the
theorem below is therefore not [AB09, Thm 6.22]". `## Divergences` opener (`:40`): "**This
is not AB's `SIZE`, and AB's theorem is not formalized.**" That opener is strong enough —
it is the first sentence, bolded, and names both halves of the claim. The theorem's own
docstring (`:291–292`) repeats it. The aggregator bullet (`CircuitComplexity.lean:63–65`)
says "**Not** [AB09, Thm 6.22]: its class is not `Language.InSIZE`" ✓.

The one bullet that stands alone without the qualifier is `## Main results` `:33–34` — "the
tree-model analogue of [AB09, Thm 6.22]" — but it sits 20 lines below the headline
disclaimer, and the declaration it names carries the qualifier. Advisory, not Blocking.

**Where the overclaim risk has actually migrated is the orchestrator's ledger, not the
file** — see the PLAN.md finding below.

### The obstruction — verified, and the `toFeedForward` claim is stronger than U11 said

**`Circuit.toFeedForward` is a cheat. Confirmed by reading it, and it is worse than the
brief's summary.** `FeedForwardCircuit.lean:250–269`: `nodes d := if d.val = 0 then Fin n
else Unit`; the single layer-0→1 gate is `{ op := { ι := Fin n, func := C.eval } }`
(`:258`) and every layer above is `FeedForward.GateOp.id Bool` (`:264`). So the map does not
embed the tree at all — it hides the entire circuit inside one opaque gate operation and
runs a wire up. Three consequences, all checkable:

1. It is `FeedForward Bool`, and `AC_GateOps : Set (GateOp (Fin 2))` (`ACpGates.lean:27`),
   so `OnlyUsesGates AC_GateOps` is not even a well-formed question about it — and
   `Language.InSIZE` only quantifies over `ACP.CircuitFamily`, which fixes `Fin 2`.
2. At the right alphabet the layer-0 op is `C.eval`, which for general `C` is none of
   `AC_GateOps`'s three members (`id`, `1 - x 0`, `∏ i, x i`).
3. **`FeedForward.size` = `Nat.card (Σ d : Fin depth, nodes d.succ)`, and `d.succ.val ≥ 1`
   always, so every non-input layer is `Unit` and `C.toFeedForward.size = C.depth + 1` —
   independent of `C.size`.** The file's own comment at `:296–297` says exactly this. A map
   whose image size does not mention the source size cannot transport a size class in
   either direction.

So U11's "cheat" is right and understated. Note which direction this does and does not
block: it happens *not* to be the direction the hierarchy needs — the missing half is
`FeedForward` → tree, and U11 identifies that correctly (`:49–51`).

**`FeedForward` → tree.** Verified: `toCircuit_eval` (`FeedForwardCircuit.lean:217–225`)
requires `hcorrect : F.IsAndOrGate isAnd gfin`; `AC_GateOps` (`ACpGates.lean:27–31`) is
`{id, NOT} ∪ ⋃ n {AND}`, so membership does not supply it, and `BoolCircuit.Circuit` has
only `lit` and `node isAnd` — no `id`, no `NOT` node. `toCircuit_size_le`
(`:227–235`) gives `(k + 1) ^ F.depth`, exponential in depth. Both halves of U11's claim
hold. (`AC_GateOps` also has no OR at all, so the two gate conditions are incomparable in
both directions; the file names only the direction that matters, which is correct.)

**Direct counting.** Verified infeasible for the stated reason: `nodes : Fin (depth + 1) →
Type v` (`FeedForwardCircuit.lean:27`) with no `Fintype`, `DecidableEq` or encoding, and
`size` is `Nat.card`-based, silently `0` on infinite layers. U10's argument runs through
`encodeCircuit` and has no analogue here.

### The constant — `10 ℓ 2^ℓ` confirmed, two independent ways

The brief's `2^ℓ · 10` was wrong; U11's `10 ℓ 2^ℓ` is right.

1. **Page image** (`pdftoppm -f 142 -l 142 -r 200`, book p.116, read directly): "every
   function from {0,1}^ℓ to {0,1} is computable by a **2^ℓ 10ℓ**-sized circuit", and the
   display line "g ∈ **SIZE(2^ℓ 10ℓ)** = SIZE(11n^{1.1} log n) ⊆ SIZE(n²)".
2. **Arithmetic, independent of any extraction.** With `ℓ = 1.1 log n`, `2^ℓ = n^{1.1}` and
   `10ℓ = 11 log n`, so `2^ℓ · 10ℓ = 11 n^{1.1} log n` — AB's own next term, exactly.
   `2^ℓ · 10 = 10 n^{1.1}` does not match it. The same check pins the lower constant:
   `2^ℓ/(10ℓ) = n^{1.1}/(11 log n)`, AB's second display line ✓.

This is the third glyph-drop in this book: `pdftotext -layout` renders the two as
`"a 2 10-sized circuit"` and `"2 /(10)"`. `ch6/PLAN.md`'s correction is **right** as
written.

Downstream: `Hierarchy.lean:59–63` quotes `10 ℓ 2 ^ ℓ`, `2 ^ ℓ / (10 ℓ)` and
`2ⁿ/n > T'(n) > 10 T(n) > n` — all three match the page ✓. "Both of ours are the sharper
number for every `ℓ ≥ 1`" checks: `2^ℓ(ℓ+1)+1 ≤ 10ℓ2^ℓ` ⟺ `2^ℓ(9ℓ-1) ≥ 1` ✓, and
`ℓ+5 < 10ℓ` ⟺ `ℓ ≥ 1` ✓. The immediate qualifier "which buys nothing across models" keeps
it honest.

### The mathematics — checked

**`restrictCircuit_size` is a genuine equality and is used soundly.** `:144–147`: a literal
inside the kept range becomes a literal (size 1); one outside becomes
`.node (l.eval pad) []`, whose size is `1 + [].foldr … 0 = 1` — the same one node. The
`isAnd` flag doubles as the constant, and `eval_node_nil` (`:110–112`) makes the empty AND
`true` and the empty OR `false`, so the substituted constant is the right one. The gate case
maps over children and `1 + ·` passes through. The single use (`:283–284`) needs only `≤`;
`rw [restrictCircuit_size]; exact hDsize n₀` is exact. `widenCircuit_size` likewise ✓.

**Constants are U9's and U10's, not AB's** ✓. `hup` is literally
`universalCircuit_size_le`'s conclusion `2 ^ ℓ n * (ℓ n + 1) + 1` (`Universal.lean:148–149`);
`hlow` is literally `exists_not_eval_of_lt`'s hypothesis `(ℓ n₀ + 4) * T n₀ < 2 ^ ℓ n₀`
(`HardFunctions.lean:223`) — the **parametric** hook, not `exists_hard_function`'s baked
`2^n/(n+5)`, which is what `ch6/PLAN.md` asked for.

**Non-degeneracy — Blocking item 3 is discharged.** `treeSize_one_ssubset` (`:324–326`)
instantiates at `T ≡ 1`, `n₀ = 3`: `(3+4)·1 = 7 < 8 = 2^3` ✓, and `HardFunctions.lean:268–272`
confirms `ℓ = 3, S = 1` has content (it excludes every literal and both empty gates).
`zero_mem_treeSize_one` (`:330–331`) puts `(0 : Language Bool)` in the *smaller* class via
`.node false []` of size 1. So the headline instance is a strict inclusion between two
nonempty classes, and it is not the empty-class artifact.

**The judgement call on the general theorem — accept it.** `TreeSize T` can indeed be empty
when `ℓ n₀ < 3`: `hlow` forces `T n₀ = 0` (at `ℓ n₀ = 0,1,2` it reads `4T<1`, `5T<2`,
`6T<4`) and `Circuit.one_le_size` makes the class empty, leaving a true but trivial
`∅ ⊂ nonempty`. Stating this in the docstring rather than adding `3 ≤ ℓ n₀` is the right
call: it matches U10's own precedent (`HardFunctions.lean:62–64` carries no `n > 1` for the
same reason), a hypothesis would not be *needed* by any consumer, and the degenerate case is
not unsound — only uninteresting. The concrete instance that avoids it is supplied. Accepted.

**`eval_eq_of_iff` is not doing anything subtle.** `:225–237`. The generalization
`∀ k w (hw : w.length = k) z, (∀ i, z i = w.get (Fin.cast hw.symm i)) → …` introduces `k` by
`intro`, so `subst hw` eliminates `k` in the ordinary direction — no `Eq.mpr` transport, no
proof-irrelevance sleight. After it, `hzw : z = w.get` is a second honest `subst`, and the
goal is `hall w` on the nose. The instantiation `key n (List.ofFn x) List.length_ofFn x` is
the only place a dependent rewrite could hide, and it discharges by `List.get_ofFn`. The
statement is genuinely `∀ n x`, not `∀ n, ∀ x in the image of some word` — every
`x : Fin n → Bool` is `(List.ofFn x).get`. Clean.

**Both directions of the size divergence are named, and it cites rather than restates**
(`:53–57`): "every literal *occurrence* costs a node and no gate can be reused, raising the
count … but it charges `1` for a `k`-ary gate where Def 6.1 charges `k - 1` vertices,
lowering it" — up and down, then "The full accounting is in `Universal.lean` and
`HardFunctions.lean`; it is not restated here." That is exactly the shape
`REVIEW_CRITERIA.md:110–117` asks for, and the two sentences it keeps are verbatim
consistent with `HardFunctions.lean:41–42`. No arithmetic is re-derived. ✓

### Advisory

- [Advisory] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:94, 205 — **namespace.**
  Every declaration here is about `BoolCircuit.Circuit`, but they sit in `ACP`, which
  `ch6/PLAN.md` *Standing conventions* now reserves for `FeedForward` ("the namespace
  follows the circuit type"). `ACP.TreeSize` ends up adjacent to `ACP.PPoly` and
  `ACP.CircuitFamily`, which are the `FeedForward`/`SIZE` objects — mild pressure in
  exactly the direction this unit spent its docstring resisting. **Not charged against
  U11:** `Universal.lean` and `HardFunctions.lean` already do this and both are `DONE`, and
  moving U11 alone would split the chain. Cross-track pass, with U9/U10 and
  `ACP.cktSatLang`.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:109–112 — `eval_node_nil` is
  a general fact about `BoolCircuit.Circuit.eval`, parked in this file and named `ACP.*`.
  `policy.md` §1 *Helpers* puts it in `Basic.lean` as `Circuit.eval_node_nil`. Queue it with
  the `Circuit.eval_lit` / `eval_node_*_iff` relocation already in `ch6/PLAN.md`'s deferred
  table.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:188 — `Language.InTreeSize`
  quantifies over a bare `(n : ℕ) → Circuit n` where `BoolCircuit.TreeCircuitFamily`
  (`NCAC.lean:90`) bundles the same data and defines `language` identically
  (`NCAC.lean:98–110`). **Cross-track — not settled here**, per the brief; U12's critic owns
  `NCAC.lean`. Two notes for the orchestrator: the file's own reason
  (`:76–80`, "that file is a parallel track") is accurate and sufficient, but the
  `policy.md` §1 *Layering* justification given in U11's report is not — §1 says to *split*
  a definition out of a heavyweight file so it can be imported, not to re-declare its data
  to avoid the import. The clean resolution is a definitions file both can import.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:23 — "the **diagonal**
  language". AB opens the proof of 6.22 with "the diagonalization methods of Chapter 3 do
  not seem to apply in this setting; nevertheless, we are able to prove Theorem 6.22 using
  the counting argument". Nothing here diagonalizes. → "the padded language".
- [Advisory] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:43–45 — the reason given for
  tree → `FeedForward` failing is the weakest true one. "one gate `⟨Fin n, C.eval⟩` that is
  not in `AC_GateOps`" is a type-level non-statement (`GateOp Bool` vs `GateOp (Fin 2)`),
  and for special `C` — an all-positive AND — the transported op *would* be in it. The
  decisive fact is one line away and unconditional: `C.toFeedForward.size = C.depth + 1`,
  independent of `C.size`. → say that instead.
- [Advisory] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:69 — "the strict inclusion
  vacuous". `∅ ⊂ TreeSize T'` is true, just trivial. → "degenerate".
- [Advisory] TCSlib/Complexity/CircuitComplexity/Hierarchy.lean:26–36 — `## Main results`
  omits `Language.InTreeSize.mono` and `Language.zero_inTreeSize`; the second is the
  ingredient that makes `zero_mem_treeSize_one` — which *is* listed — mean anything.
  `## Main definitions` omits `ACP.extendBy`. Same advisory U4 drew.

### The four orchestrator edits, reviewed as an agent's

1. **Aggregator registration** — correct. Import at `CircuitComplexity.lean:16`, bullet at
   `:63–65`, build reproduces at **3047 jobs**. The bullet is honest and names the class
   distinction. ✓
2. **`ch6/NOT_FORMALIZED.md` Thm 6.22 row** (`:19`) — content is right, and it cites
   `Hierarchy.lean`'s `## Divergences` instead of restating it, per `REVIEW_CRITERIA.md:110`.
   "no theorem there is named for 6.22" verified by `grep` ✓. The follow-up line `:77`
   ("*not* Theorem 6.22, see its row above") closes the contradiction with the
   "Formalized in wave 2" list ✓. **One defect: placement.** The row is in the table headed
   "## §6.1, pp. 108–111 — **the completed range**", but Theorem 6.22 is §6.6, p.116. It
   belongs under "## §§6.3–6.8, pp. 113–122", where U12's two rows were filed for the same
   reason. Filing 6.22 inside "the completed range" is the one thing in this ledger that
   could later be misread as a claim.
3. **`ch6/PLAN.md` AB-constant correction** — **verified correct**, two ways, above. ✓
   **But the U11 entry is now the largest remaining overclaim risk in the loop.** It is
   still titled "### U11 — Theorem 6.22: nonuniform hierarchy" and still describes the
   deliverable as "`SIZE(T) ⊊ SIZE(T')` for suitable `T < T'`". Flipping that heading to
   `DONE` unchanged would make the orchestrator's own ledger assert that 6.22 was delivered
   — the precise failure the file spent its docstring avoiding, and in a heading rather than
   a docstring. Retitle to name the tree-model deliverable and point at the
   `NOT_FORMALIZED.md` row **before** any flip.
4. **`CircuitSat.lean:39–44`** — the substance is right and the old reason was indeed false.
   Verified each new clause: `AC_GateOps` (`ACpGates.lean:27–31`) does contain `GateOp.id`
   and `⟨Fin 1, 1 - x 0⟩`, and `BoolCircuit.Circuit` has neither node ✓;
   `FeedForward.nodes : Fin (depth+1) → Type v` (`FeedForwardCircuit.lean:27`) carries no
   `DecidableEq`/`Fintype`, where `CktVar n` needs one to key Tseitin variables ✓.
   **One imprecision:** `ACp_GateOps_cases` (`ACpGates.lean:585`, line number exact) is
   stated for `op ∈ ACp_GateOps p` with `[Fact (Nat.Prime p)]`, not for `op ∈ AC_GateOps`;
   `ACp_GateOps` is `AC_GateOps ∪ ⋃ n {modGateOp p n}` (`:119–120`) and no `AC_GateOps_cases`
   exists. It does unfold the `⋃` with `Set.mem_iUnion.mp`, so the point stands — but as
   written the docstring cites a lemma about a different set. → "…*can* be cased on; the
   `⋃` unfolds by `Set.mem_iUnion`, as `ACP.ACp_GateOps_cases` (`ACpGates.lean:585`) does
   for the superset `ACp_GateOps`."

### One cross-file finding the orchestrator should route

- [Advisory] TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean:92–95 — the
  module comment says of tree → DAG: "a tree is already a DAG with fanout ≤ 1, so the
  embedding **is faithful**. The FeedForward circuit has the same depth and its size is at
  most `C.size * C.depth` after inserting identity wires to pad shorter branches". None of
  that describes `:250–269`. There is no branch padding and no structural embedding: layer 0
  is one gate holding `C.eval` whole, every other layer is a single identity wire, and the
  size is exactly `C.depth + 1`. The `C.size * (C.depth + 1)` bound at `:299` is true only
  because it is enormously loose. This is prose asserting more than the code does, in a file
  `ch6/PLAN.md`'s deferred table already cites as the missing `CircuitFamily` ↔ `Circuit`
  bridge — and U11 is the first unit to have actually read the map. Not U11's file; route it.

### What round 2 needs

Only the two Blocking items — one sentence swapped at `:289–291`, and `foldr_congr` replaced
by `List.foldr_ext` at four call sites. The mathematics, the constants, the non-degeneracy
argument, the obstruction analysis and the framing all stand as written; do not touch them.
`ch6/PLAN.md` U11 stays `WIP`.

## U11 — round 2 — PASS

Both round-1 Blocking items are addressed, five advisories applied, and **zero Blocking
remain in `Hierarchy.lean`**. `ch6/PLAN.md` U11 flipped to `DONE`.

Two defects remain, and neither is U11's: one is a **botched edit in `CircuitSat.lean`**
that must be fixed before commit, and one was a **false sentence in the `ch6/PLAN.md` U11
entry** that I corrected as part of the flip rather than stamp `DONE` on top of. Details
below.

### Round-1 Blocking — both closed

- **B1 `:280–282`** — now "a padding length `ℓ` **long enough** that [AB09, Thm 6.21] bites
  at some length `n₀` and **short enough** that [AB09, Claim 2.13] still fits inside `T'`".
  Correct, and it is the direction the code has. Re-derived independently rather than
  trusting the report: `hlow` at `T n₀ = 1` fails at `ℓ = 2` (`6 < 4`) and first holds at
  `ℓ = 3` (`7 < 8`); `hup` at `T' n = 33` holds at `ℓ = 3` (`33 ≤ 33`) and fails at `ℓ = 4`
  (`81 ≤ 33`). Dropped.
- **B2 `:101–107`** — `foldr_congr` deleted, `grep` empty. All four sites now
  `List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc]` (`:122`, `:131`, `:155`, `:164`),
  zero glue, no `simp` added to absorb the argument-order change. Dropped.

### Advisories — five applied, one left with cause

Dropped: "the diagonal language" → "the padded language and its circuits" (`:22`);
"vacuous" → "the strict inclusion would separate nothing" (`:73–74`); `## Main results`
headline bullet now carries **"and not that theorem, whose class is `Language.InSIZE`"**
(`:34–36`), so the disclaimer no longer depends on a reader having reached the header three
sections up; `Language.InTreeSize.mono` and `Language.zero_inTreeSize` added (`:30–31`).
`eval_node_nil` correctly left for the cross-track pass — `Basic.lean` is held by another
agent this round.

The `toFeedForward` advisory is applied and the fix is right (`:47–49`): "every layer above
the input is `Unit`, so its size is `C.depth + 1` whatever `C.size` is, and a map whose
image size never mentions its source's cannot transport a size class either way." Note the
older clause "that is not in `AC_GateOps`" survives beside it. I asked for it to be replaced
rather than joined, but it is now harmless: it follows "which is over `FeedForward Bool`,
not `Fin 2`" in the same sentence, so the type mismatch is already in the reader's hand, and
it is no longer the load-bearing reason. Not re-raised.

One unlisted improvement worth recording: `## Main results` `:27–29` now attributes the
pull-back step to `restrictCircuit_eval_of_onFirst` rather than to `restrictCircuit`. That
is the declaration that actually performs [AB09, p.116]'s step; the round-1 wording named
the reindexing instead. Correct on its own initiative.

### The `eval_eq_of_iff` trim — the two lines say enough

`:213–215`: "Every assignment is a `w.get` for `w = List.ofFn x`; `key` generalizes the
length so that reaching it is a `subst` rather than a dependent rewrite."

That is the whole content. It names the surjectivity fact that makes the lemma **true**, and
the one structural choice a reader would otherwise have to reverse-engineer — why an
auxiliary `∀ k w (hw : w.length = k)` exists at all when the statement quantifies over `n`.
What was cut was the `Bool.eq_iff_iff` step, which is visible in the first tactic line and
needed no prose. Good trim; the remaining two lines are the right two.

### The ratio — healthy, and the anxiety is misplaced

`awk`, verbatim, reproduces the reported figure exactly:

```
total=324 code=144 comment=142 blank=38
```

Flagging the 2-line margin rather than burying it is right. The conclusion drawn from it is
not. **Strip only the two spans Blocking item 0 exempts** — `## Divergences` (`:40–79`) and
`## References` (`:86–89`) — and re-run the same command:

```
non-exempt: total=280 code=144 comment=98 blank=38
```

**98 against 144.** The margin is 46 lines, not 2. The tight raw count is *entirely* the 44
lines of content that Blocking item 2 **requires** and item 0 exempts for exactly this
reason — a short file carrying a mandated divergence block will always sit near 1:1 on the
raw count, and item 0 exists so that is not held against it. The file is not carrying excess
prose.

The warning that matters is the opposite one: **do not trim explanation in a future round to
buy raw-ratio headroom.** The near-miss at `146 > 144` came from *deleting eight lines of
code* (`foldr_congr`), not from adding prose, and reusing Mathlib is the correct move
regardless of what it does to a ratio. If a round genuinely needs room, `## Implementation
notes` (`:80–84`) is the right five lines to reconsider, as the unit itself identified —
it records a cross-track note, not a divergence.

Docstring `:9–90` = 82; exempt `## Divergences` 40 + `## References` 4; **38 non-exempt**
against the ~40 cap ✓ — tighter than round 1's 37, and the two lines went to the
`## Main results` disclaimer, which is the best possible place to have spent them.

### Measurements — all re-run

| check | result |
|---|---|
| `lake build …Hierarchy` | **1032 jobs, exit 0** ✓ (unchanged from round 1) |
| `lake build TCSlib.Complexity.CircuitComplexity` | **3047 jobs, exit 0** ✓ |
| `lake build` (full) | **3701 jobs, exit 0** ✓ |
| `zsh scripts/lean_check.sh` | no output, **exit 0** ✓ |
| `grep sorry\|admit\|native_decide\|foldr_congr` | empty ✓ |
| axiom sweep (module index, **no `!nm.isInternal` guard**) | `declarations scanned: 51 (internal/mangled 15); union = [propext, Quot.sound, Classical.choice]; sorryAx users: []` |

The **52 → 51** drop reproduces, and the accounting for it is right: `foldr_congr` left the
module and `List.foldr_ext` is indexed to Mathlib, so it contributes no constant here. Run
from `U11cR2Sweep.lean`, written immediately before the run.

No statement changed this round — checked against my round-1 reading of the whole file, not
accepted on report. Every `def` and `theorem` signature is character-identical to round 1
and only its line number moved (each shifted up by 5 above `end ACP`, by 9 below it, which
is the two deletions); the four `List.foldr_ext` sites are the only tactic lines that
differ. `code` moved 151 → 144 by exactly `foldr_congr`'s seven lines of Lean
(round 1 `:101–107`); its docstring was the eighth line and counted as comment.

### The two remaining defects — both in the orchestrator's edits, not in U11

- [Blocking, **not against U11**] TCSlib/Complexity/CircuitComplexity/CircuitSat.lean:39–40
  — **the rewording is a botched edit.** The text now reads:

  ```
  tree is forced, though not for the reason earlier drafts of this file gave: a gate's
  a gate's membership in these gate sets *can* be cased on: `ACP.ACp_GateOps_cases`
  ```

  "a gate's" is duplicated across the line break, leaving an ungrammatical fragment in a
  `DONE` file's module docstring. → delete the trailing "a gate's" on `:39`. The *substance*
  of the replacement is correct and I verified every clause of it independently:
  `ACp_GateOps_cases` is at `ACpGates.lean:585` and is stated for `op ∈ ACp_GateOps p` ✓;
  `ACp_GateOps = AC_GateOps ∪ ⋃ n, {modGateOp p n}` at `:119–120` ✓; it unfolds the `⋃`
  through `Set.mem_iUnion.mp` ✓; no `AC_GateOps_cases` exists ✓ and nothing obstructs one ✓.
  I am not holding U11 for this — it is U3's file and the unit under review is
  `Hierarchy.lean` — but it must not be committed as it stands.

- [Fixed by me, as part of the flip] ch6/PLAN.md, U11 entry — the retitle is right and the
  new deliverable paragraph is accurate, but the entry's **last sentence still read "Builds
  on `Language.InSIZE` and `InSIZE.mono`", which is false.** `Hierarchy.lean` imports only
  `HardFunctions` and `Universal`; `PPoly.lean` is not in its import set, and `InSIZE`
  occurs in the file only inside the four sentences that say the class here is *not* it.
  Stamping `DONE` on an entry claiming the unit builds on `InSIZE` would have frozen into
  the ledger the precise misreading this unit spent its docstring preventing — the round-1
  finding about the old heading, one sentence further down. Rewritten to "Builds on U9 and
  U10 only — `PPoly.lean` is not imported, and `Language.InSIZE` is named in
  `Hierarchy.lean` solely to say the class here is not it."

### The other three orchestrator edits — checked, all correct

- **`NOT_FORMALIZED.md`** — the Thm 6.22 row is now at `:71`, inside the
  "## §§6.3–6.8, pp. 113–122 — surveyed in full" table (`:52`), out of "the completed
  range". Correct, and it matches where U12's rows were filed. ✓ (Unrelated and
  pre-existing: the file header still reads "Sources: AB pp. 108–113 (PDF 134–139)", which
  three sections of the file have outgrown.)
- **`ch6/PLAN.md` deferred table `:275`** — the routed `FeedForwardCircuit.lean:92–95`
  finding is stated accurately, quotes the prose it contradicts, gives the three facts that
  contradict it, and correctly records the file as off-limits without the user's say-so. ✓
  One citation nit: `Circuit.toFeedForward` is declared at `:250`; `:256` is inside its
  body and the gate op is at `:258`.
- **`ch6/PLAN.md` bridge row** — corrected alongside, and now says both directions fail with
  the right reason for each. It no longer understates `toFeedForward`. ✓

### Verdict

`Hierarchy.lean` is done. The mathematics was sound in round 1 and is untouched; what
changed is prose that now matches it, and one Mathlib lemma in place of a copy. The framing
held up under two rounds of adversarial reading: nothing is named `SIZE`, no theorem is
named for 6.22, and the disclaimer now appears at the headline, in `## Main results`, in
`## Divergences`, on the theorem, in the aggregator bullet, in the `NOT_FORMALIZED` row and
in the `PLAN` heading. U11 → `DONE`.

Carried to the cross-track pass: `ACP.*` namespace for `Circuit` machinery (with U9/U10);
`eval_node_nil` → `Basic.lean`; `Language.InTreeSize` vs `BoolCircuit.TreeCircuitFamily`.

---

## U12 — round 3 — REVISE

**Round 2's Blocking is fixed, the naming advisory is fully applied, and all three
corrections were accepted. The rename is sound in the code.** But the sweep you asked me to
run found a **third** casualty of the `Circuit.Circuit. → Circuit.` guard, in the one file
the unit's own grep did not reach — and it is in the `## Main definitions` block of
`Basic.lean`, the shared foundation. The unit wrote the rubric rule for this defect class
this round and then shipped an instance of it. One bullet; nothing else is open.

### The third casualty — found mechanically, not by reading

I ran two independent sweeps.

**1. Resolution sweep.** Extracted every backticked identifier from every comment and
docstring in the three files — 209 occurrences, 107 distinct — and resolved each against
the live environment (`env.constants`, matching bare, `BoolCircuit.`-, `Language.`-,
`ACP.`-prefixed and trailing-component forms, so `private` declarations count as found).
24 came back unresolved; 23 are prose or file/module names (`AND`, `OR`, `NOT`, `PARITY`,
`L`, `w.length`, `Basic.lean`, the four `TCSlib.…` module paths, the `_nil`/`_cons`/`_eval_zero`
style suffix shorthands) or an artifact of my import set (`DNF`, which is in `Formulas.lean`).
**One is a real dangling name.**

**2. `git diff HEAD` cross-check**, which is decisive because `HEAD:Basic.lean` *is* the
pre-U12 state of that file. Exactly two lines lost a `BoolCircuit.Circuit.` segment:

```
-theorem _root_.BoolCircuit.Circuit.one_le_size (C : Circuit n) : 1 ≤ C.size := by
-* `BoolCircuit.Circuit.toNAnd` / `toNOr` — normalization into that form;
```

The first is the intended hoist. The second is the casualty, and it is a **regression**:
`HEAD` had it right.

- [Blocking] `TCSlib/Complexity/CircuitComplexity/Basic.lean:31` — `` `BoolCircuit.toNAnd` ``
  in `## Main definitions` names a declaration that does not exist. The declaration is
  `Circuit.toNAnd` (`Basic.lean:441`) inside `namespace BoolCircuit`, i.e.
  `BoolCircuit.Circuit.toNAnd`, which is what the line said before this round's rename; the
  `Circuit.Circuit. → Circuit.` guard ate the segment here exactly as it did at
  `NCAC.lean:20` and `:493`. Every sibling bullet in the same block gives a resolvable full
  name (`BoolCircuit.Lit:23`, `BoolCircuit.Circuit:25`, `BoolCircuit.NAndCircuit:29`), so
  this one is inconsistent as well as broken. Rubric item 6 makes the `## Main definitions`
  block mandatory content; a mandatory block naming a nonexistent declaration is a defective
  one. → `` `BoolCircuit.Circuit.toNAnd` / `toNOr` ``. The trailing `toNOr` is fine as
  shorthand once the first name resolves.

**The finding worth more than the typo is what it says about the safety net.** The unit
reported catching the docstring casualty "by grepping every `BoolCircuit.` occurrence
against what should carry a `Circuit.` segment". That procedure, run over all three touched
files, finds this one too — `BoolCircuit.toNAnd` is in the output of a plain
`grep -o "BoolCircuit\.[A-Za-z_][A-Za-z0-9_'.]*"` on `Basic.lean`. So the grep was run over
`NCAC`/`Parity` but not over `Basic`, or against the fourteen renamed names rather than
against every `BoolCircuit.` occurrence — and the guard did not care which name followed it.
Self-catching two of three is genuinely good practice and I do not want to discourage it;
the lesson is that the sweep has to cover every file the script touched, not every name the
script was aimed at.

### Round-2 Blocking — fixed, with the right wording

`NCAC.lean:42-46` now reads "…duplicates a node once per consumer, **blowing the node count
up by a factor of at most `f ^ d`**, so the fan-out-1 restriction is expected to be harmless
exactly where **a polynomial-size family stays polynomial**: on the `NC` side at `i = 1`
(`f = 2`, `d = O(log n)`), and on the `AC` side at `i = 0` (`f = poly(n)`, `d = O(1)`)." The
false node count is gone, the quantity is named as a factor, and "a polynomial-size family
stays polynomial" does close the `S`-shaped hole — the sentence now carries its own
conclusion instead of leaning on a reinterpretation of its subject. The `i`-indices and their
parameters are unchanged and still correct, and the "the two indices differ" sentence
survives. **Dropped.**

### Round-2 Advisory — naming: applied in full, and further than asked

All fourteen unfoldings are now `Circuit.`-scoped (`Basic.lean:198-268`), joining
`Circuit.maxFaninL:194`, `Circuit.one_le_size:188`, `Circuit.maxFanin_le_size` and
`Circuit.size_succ_le_two_pow`. They now sit in one unbroken run with the pre-existing
`Circuit.maxDepth:171` / `Circuit.sumSize:175`, which is the consistency the advisory was
after, and the `NAndCircuit`/`NOrCircuit` collision at `Basic.lean:333,340` is now
structurally impossible rather than merely unhit. Verifying first that none of the fourteen
names occurs elsewhere in `TCSlib/` was the right precaution. **Dropped.** The other four
round-2 Advisories are all disposed: `NOT_FORMALIZED.md:72` moved to the three-column table
with status `BLOCKED`; `:75-78` rewritten as "Formalized in wave 2" and now accurate;
`REVIEW_CRITERIA.md` dropped the 64-vs-610 ratio and added the transitivity note at `:140`.

### The three corrections — accepted, and correctly

- **"No tactic changed anywhere" withdrawn** in favour of "no mathematical content changed".
  That is the claim that is both true and checkable, and it is the right lesson: the
  absolute was wrong by three lines last round and by 94 this round, all of them
  requalification landing inside `simp only`, `rw` and `have` ascriptions. Quoting
  `Basic.lean +149/−3` and `FeedForwardCircuit.lean −6` where a baseline exists, and saying
  so where one does not, is the correct form.
- **Full build 3701**, confirmed by my own run; `Hierarchy.lean` entering the reachable set
  accounts for it. Stating the registration state alongside the figure is the fix for what
  has now bitten three rounds running.
- **Axiom-sweep framing.** The self-assessment — over-claiming "in the same shape as the
  `f ^ d` bullet — reading a constant count as a declaration count and a narrow gap as a
  hole" — is exactly right, and the breakdown it now reports is the useful artifact.

### Measurements — all re-run, unit-numbered scratch, all match

- `lake build` (full) — **3701, exit 0** ✓. `lake build TCSlib.Complexity.CircuitComplexity`
  — **3047, exit 0** ✓.
- `zsh scripts/lean_check.sh` — no output, `rc=0` on all three ✓.
- `grep sorry|admit|native_decide` — empty ✓.
- Mandated `awk`, verbatim, all three ✓:

  ```
  Basic   total=674 code=380 comment=214 blank=80
  NCAC    total=531 code=331 comment=136 blank=64
  Parity  total=404 code=265 comment=95 blank=44
  ```

- Axiom sweep re-run independently, with the private breakdown:

  ```
  Basic:  total=374 nonInternal=228 private=46  [Quot.sound, Classical.choice, propext]  sorryAx=[]
  NCAC:   total=139 nonInternal=45  private=81  [Quot.sound, Classical.choice, propext]  sorryAx=[]
  Parity: total=97  nonInternal=11  private=80  [Quot.sound, Classical.choice, propext]  sorryAx=[]
  GRAND total=610 private=207
  ```

  **610 and 207 confirmed to the unit**, no `sorryAx`, nothing outside the three axioms.
- Line length in **characters** (Python, per the new rule): max 97 / 99 / 91, **none over
  100** ✓. The new rubric note is correct — `awk`'s `length` counts bytes, and the lines
  that looked long carry `ᵏ`, `∧`, `ⁱ` at three bytes each.
- Non-exempt docstrings: `Basic` `18–72`=55 less Div `46–56`=11 less Ref `68–71`=4 → **40**
  (down from 41, and now at the cap rather than over it); `NCAC` `11–78`=68 less Div
  `34–73`=40 less Ref `74–77`=4 → **24**; `Parity` → **17**. All ✓.

### Advisory

- [Advisory] `ch6/REVIEW_CRITERIA.md:113-114` — the new rule's own tally is now wrong: "one
  call site (caught by `lake build`) and **one** docstring reference (not caught by
  anything)". There were **two** docstring references, and the second is the Blocking above.
  → "…and two docstring references, one of which the unit's own post-rename grep also
  missed, because it was run over the files the rename targeted rather than over every file
  the script wrote to." The rule itself is right, well-placed, and would have caught this;
  it is worth recording that its first application was incomplete, since that is the part a
  future unit will get wrong the same way.

### Verdict

**REVISE** — one Blocking, `Basic.lean:31`, two tokens. No Lean semantics are involved and
nothing else in the round is open.

A note on where this unit's three rounds went, since the pattern is now unmistakable. Every
Blocking finding against U12 has been a sentence in a docstring, and the Lean has been
correct and essentially untouched since round 1. Round 1: an unproved class-preservation
claim and a false "not statable". Round 2: a false node count introduced while fixing round
1. Round 3: a declaration name destroyed by the script that fixed round 2's advisory. Three
different causes, one target. The compiler checks the mathematics and checks nothing else in
these files, and every defect has landed in the unchecked part — which is now three rubric
rules' worth of accumulated evidence that the unchecked part needs its own sweep, run over
every file touched, every round. The unit has been right about the mathematics throughout
and has fixed every finding at the source rather than patching it; that is why this is a
two-token round and not a fourth substantive one.

---

## U12 — round 4 — PASS

**Zero Blocking.** The fix is in and is a true revert; the sweep is real, and I rebuilt it
independently rather than checking theirs; the classification of the unresolved set holds
under my own re-derivation, including the two categories a constant lookup cannot see. Two
methodology Advisories, one of which I demonstrated experimentally and which matters beyond
this unit.

### The fix

`Basic.lean:31` reads `` * `BoolCircuit.Circuit.toNAnd` / `toNOr` — normalization into that
form; ``. `git diff HEAD -- Basic.lean | grep "BoolCircuit\.Circuit\."` returns it as a
**context** line, not a `-`/`+` pair — byte-identical to the pre-U12 state, which is the
right outcome for a line this unit never had business touching.
`grep -rn "BoolCircuit\.toNAnd\|BoolCircuit\.toNOr" TCSlib/` is empty. Both verified.

**The diagnosis it chose is the correct one and is the harder one to have accepted.** The
grep was aimed at the fourteen renamed names, so no pattern it ran could have produced
`toNAnd` in *any* file — the blind spot existed in `NCAC` and `Parity` too and merely had
nothing to find there. The corollary it draws — *a mechanical edit's blast radius is its
substitution pattern, not its intent* — is the right general form, and `BoolCircuit.Circuit.`
being an unenumerated superset of `Circuit.Circuit.` is exactly how the gap opened.

### The sweep — rebuilt, not audited

I wrote my own comment state machine (nested `/- -/`, `/--`, `/-!`, `--`) and my own
resolver rather than read theirs, so the two are independent implementations.

**Extraction reproduces to the span: 382 backticked spans, 235 identifier-shaped, 115
distinct.** Two independently written scanners agreeing on all three counts is strong
evidence the extraction is right.

**Resolution: 115 candidates, 84 resolved, 31 unresolved** against their 82/33. The
difference is my wider prefix list (`Bool.`, `BoolCircuit.TreeCircuitFamily.`), so **my
unresolved set is a proper subset of theirs** — their classification covers mine, and the
two extra names they class as binders are ones I resolve as real constants, which is an
error in the harmless direction. The `_private.<module>.0.<name>` component-suffix clause is
necessary and correct; without it `combine`, `xorNode`, `xorTree`, `xorAll`, `pairDepth`,
`pairFanin` and `clause` all read as broken. `BoolCircuit.Circuit.toNAnd` is among the
resolved.

**I classified all 31 myself, from the source line each occurs on**, and checked by hand the
two categories a constant lookup structurally cannot validate:

- **5 module paths** — `TCSlib.Complexity.CircuitComplexity.{Basic,Formulas,NCAC,Parity}`,
  `TCSlib.BooleanAnalysis.LMN.NormalFormConversion`: **all five files exist** ✓
- **3 file names** — `Basic.lean`, `Formulas.lean`, `PPoly.lean`: **all exist** ✓
- **7 name fragments** — `_nil`/`_cons` (Basic's Main results) and `_maxFanin_le`/`_depth_le`/
  `_size_le`/`_eval_zero`/`_eval_one` (Parity's): **each reconstructs to a real declaration**,
  `parityCircuit_maxFanin_le:322`, `_depth_le:329`, `_size_le:341`, `_eval_zero:360`,
  `_eval_one:365` ✓
- **6 prose** — `AND`, `OR`, `NOT` as gate names, `PARITY` as AB's name for the language,
  `L` as the variable of the statement described, `Authors` as the header field the
  Provenance paragraph points at ✓
- **10 binders/expressions/tactic** — `b d f k m n w x`, `w.length`, `induction` ✓

**The classification is sound.** No entry is a broken reference.

### The control — sound but mislabelled, and weaker than it looks

Two things, and the second is the one I was asked about.

**Terminology.** What was run is a **positive control**: inject a known defect, confirm the
test fires. A *negative* control is the clean run reporting nothing, which the 33-benign
classification already is. Worth fixing in the rubric, because "negative control" naming a
positive one will send the next unit looking for the wrong thing.

**"A check that has never failed is not yet evidence" is exactly right** and deserves its
standing rule. But the control re-injects *the defect the sweep was written for*, which
establishes the plumbing fires and nothing about reach.

**The `BoolCircuit.`-prefix discriminator is a post-hoc fit, and I tested it rather than
asserting it.** On scratch copies outside the repo I injected three docstring breaks of
*different* shapes: `Circuit.eval_lit` → `Circuit.eval_lits` (bare `Circuit.` prefix),
`Language.mem_parity_iff` → `Language.mem_parity_if` (`Language.` prefix), and
`_size_le` → `_size_lt` (fragment typo). Result:

```
CAUGHT by sweep: [Circuit.eval_lits, Language.mem_parity_if, _size_lt]
MISSED by sweep: []
of the caught, BoolCircuit.-prefixed: []
```

**The sweep catches 3 of 3. The prefix discriminator would catch 0 of 3.** The round-3 break
was `BoolCircuit.`-prefixed only because that guard's pattern strips a segment from
`BoolCircuit.Circuit.X`; a break from a typo, a moved namespace or a renamed bare lemma has
no such signature. What does the real work is the **closed taxonomy** — module path, file
name, declared fragment, prose, binder, and nothing else admitted — not the prefix. Keeping
the prefix as *the* discriminator would reproduce the unit's own diagnosis one level up:
checking against the shape of the known bug rather than the reach of the check.

- [Advisory] `ch6/REVIEW_CRITERIA.md`, the new control rule — call it a **positive** control,
  and require the injected defect to differ in shape from the one that prompted the check.
  Record that the `BoolCircuit.`-prefix signal is specific to a `…Circuit.Circuit.…`
  substitution and is not a general break-detector; the taxonomy is.
- [Advisory] the **"deliberate name fragment"** bucket is the one place where "unresolved and
  benign" is a judgement rather than a fact: `_size_lt` sits in the unresolved list
  indistinguishably from `_size_le`, and my injection confirms a typo there is invisible to
  the sweep alone. → Require each fragment to be reconstructed against a real declaration,
  as I did for all five `parityCircuit_*` this round. It is the one residual hole in an
  otherwise closed method.

### Measurements — all re-run, all match

- `lake build` full **3701**, aggregator **3047**, exit 0 ✓ · `lean_check.sh` rc=0, no
  output, all three ✓ · no `sorry`/`admit`/`native_decide` ✓
- `awk` verbatim: `Basic total=674 code=380 comment=214 blank=80` /
  `NCAC total=531 code=331 comment=136 blank=64` / `Parity total=404 code=265 comment=95 blank=44` ✓
- Axiom sweep unchanged: **610 constants, 207 `_private`**, all
  `[Quot.sound, Classical.choice, propext]`, **no `sorryAx`** ✓
- Line length in characters: max **97 / 99 / 91**, none over 100 ✓
- Repo clean: no scratch files, and my injection copies never touched it —
  `grep` for the three injected names across `TCSlib/` is empty ✓

### On the three rounds

Its diagnosis is better than mine and I adopt it: *each time it verified the thing it
changed rather than the thing its change could reach* — the class-preservation claim against
its intent rather than its literal content, the node count against the reading it meant
rather than the one it wrote, the rename against its target list rather than its
substitution pattern. One failure mode wearing three costumes.

One thing that belongs in this record and is mine, not the unit's: round 3's defect was
introduced by a script run to satisfy **my** round-2 naming advisory, and I wrote that
advisory without asking for the edit's blast radius to be bounded. The rubric now carries
the rule; the advisory that caused the need for it did not. A critic who asks for a
mechanical rename owns the sweep that follows it.

### Verdict

**PASS** — zero Blocking. Both Advisories are about the method, not the file; neither
touches Lean.

The unit ends where it should. `Language.InNC`/`InAC` are AB's Defs 6.24 and 6.25 over a
tree model, `NC^i ⊆ AC^i ⊆ NC^{i+1}` and `NC = AC` are theorems of it, `PARITY ∈ NC¹` is
proved from the dual-pair construction the model forces, and the `## Divergences` block now
says exactly what is and is not established about AB's DAG classes — including, in both
directions, how `Circuit.size` differs from Def 6.1. The mathematics was right in round 1
and is unchanged; four rounds bought an accurate account of what it means.

U12 → `DONE`. With U11 already landed, every unit in `ch6/PLAN.md` is closed. The one item
carried forward is `ACP.cktSatLang`'s namespace, for the cross-cutting pass.
