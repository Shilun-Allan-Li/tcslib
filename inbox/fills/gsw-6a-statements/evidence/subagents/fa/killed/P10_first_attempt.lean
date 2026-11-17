import TCSlib.Complexity.CircuitComplexity.FormulaArith
import Mathlib.Algebra.BigOperators.Fin

/-!
# Probe P10: formula arithmetic (brief check 7)

Every check below is a closed Boolean computed by `#eval` (the formula semantics
`TreeCircuit.eval`/`depth`/`maxFanin` and Mathlib's `Nat.clog` are well-founded definitions that
the kernel does not reduce, so `decide` cannot be used on them); each `#eval` prints the number
of failures (expected `0`) and the number of cases checked.  The closed form of `csaLevels`
(structural, kernel-reducible) is also checked by kernel `decide +kernel` against a structural
surrogate of `Nat.clog 2` (`clogS`), whose agreement with `Nat.clog 2` is `#eval`-checked.
No `native_decide`.
-/

open BoolCircuit BoolCircuit.FormulaArith

namespace P10

/-- the `j`-th variable as a positive literal -/
def v {n : ℕ} (i : Fin n) : TreeCircuit n := .lit ⟨i, true⟩

/-- all assignments of `n` variables, from the bits of `m < 2 ^ n` -/
def assigns (n : ℕ) : List (Fin n → Bool) :=
  (List.range (2 ^ n)).map fun m i => m.testBit i

/-- count failures and cases -/
def tally (l : List Bool) : ℕ × ℕ := (l.countP (· = false), l.length)

/-! ## 1. Gadget truth tables (F3) -/

#eval tally ((assigns 3).map fun x =>
  (TreeCircuit.xor3 (v 0) (v 1) (v 2)).eval x == (x 0 ^^ x 1 ^^ x 2))
#eval tally ((assigns 3).map fun x =>
  (TreeCircuit.maj3 (v 0) (v 1) (v 2)).eval x == (x 0 && x 1 || x 2 && (x 0 ^^ x 1)))
#eval tally ((assigns 2).map fun x =>
  (TreeCircuit.xor2 (v 0) (v 1)).eval x == (x 0 ^^ x 1) &&
  (TreeCircuit.and2 (v 0) (v 1)).eval x == (x 0 && x 1) &&
  (TreeCircuit.or2 (v 0) (v 1)).eval x == (x 0 || x 1) &&
  (TreeCircuit.const true : TreeCircuit 2).eval x == true &&
  (TreeCircuit.const false : TreeCircuit 2).eval x == false)
-- gadget depths over literals (r3: +1, +1, +2, +4, +3) and constants (1)
#eval ((TreeCircuit.and2 (v (0 : Fin 3)) (v 1)).depth, (TreeCircuit.or2 (v (0 : Fin 3)) (v 1)).depth,
  (TreeCircuit.xor2 (v (0 : Fin 3)) (v 1)).depth, (TreeCircuit.xor3 (v (0 : Fin 3)) (v 1) (v 2)).depth,
  (TreeCircuit.maj3 (v (0 : Fin 3)) (v 1) (v 2)).depth, (TreeCircuit.const true : TreeCircuit 3).depth)
-- gadget fan-ins (all 2)
#eval ((TreeCircuit.xor3 (v (0 : Fin 3)) (v 1) (v 2)).maxFanin,
  (TreeCircuit.maj3 (v (0 : Fin 3)) (v 1) (v 2)).maxFanin)
-- depth +4 / +3 with unequal argument depths
#eval ((TreeCircuit.xor3 (TreeCircuit.xor3 (v (0 : Fin 3)) (v 1) (v 2)) (v 1) (v 2)).depth,
  (TreeCircuit.maj3 (v (0 : Fin 3)) (v 1) (TreeCircuit.xor3 (v 0) (v 1) (v 2))).depth)

/-! ## 2. Negation, substitution, renaming (F1–F2) on samples -/

def sample : TreeCircuit 3 :=
  .node false [TreeCircuit.and2 (v 0) (.lit ⟨1, false⟩), .node true [v 2, .lit ⟨0, false⟩, v 1], v 2]

#eval tally ((assigns 3).map fun x => sample.neg.eval x == !sample.eval x)
#eval (sample.neg.depth == sample.depth, sample.neg.maxFanin == sample.maxFanin)
def f3 : Fin 3 → TreeCircuit 2 := ![TreeCircuit.xor2 (v 0) (v 1), .lit ⟨1, false⟩,
  TreeCircuit.const true]
#eval tally ((assigns 2).map fun x =>
  (sample.subst f3).eval x == sample.eval fun i => (f3 i).eval x)
#eval ((sample.subst f3).depth, sample.depth, (sample.subst f3).maxFanin)
#eval tally ((assigns 2).map fun x =>
  (sample.rename ![(1 : Fin 2), 0, 1]).eval x == sample.eval (x ∘ ![(1 : Fin 2), 0, 1]))
#eval ((sample.rename ![(1 : Fin 2), 0, 1]).depth == sample.depth)

/-! ## 3. Numbers: constant words of every length ≤ 3 over one dummy variable -/

/-- the word of length `L` with bits of `m`, as constant formulas -/
def cw (L m : ℕ) : List (TreeCircuit 1) := (List.range L).map fun j => .const (m.testBit j)
def words : List (List (TreeCircuit 1)) :=
  (List.range 4).flatMap fun L => (List.range (2 ^ L)).map (cw L)
def x0 : Fin 1 → Bool := fun _ => false

-- F5 value equation, all 15³ triples of constant words
#eval tally (words.flatMap fun A => words.flatMap fun B => words.map fun C =>
  val x0 A + val x0 B + val x0 C == val x0 (csaStep A B C).1 + val x0 (csaStep A B C).2)
-- F5 value equation on literal words, all 64 assignments
def LA : List (TreeCircuit 6) := [v 0, v 1]
def LB : List (TreeCircuit 6) := [v 2]
def LC : List (TreeCircuit 6) := [v 3, .lit ⟨4, false⟩, v 5]
#eval tally ((assigns 6).map fun x =>
  val x LA + val x LB + val x LC == val x (csaStep LA LB LC).1 + val x (csaStep LA LB LC).2)
-- F5 depth +4 (counted from max 1 _), fan-in
#eval (TreeCircuit.maxDepth ((csaStep LA LB LC).1 ++ (csaStep LA LB LC).2),
  TreeCircuit.maxFaninL ((csaStep LA LB LC).1 ++ (csaStep LA LB LC).2))

-- F6: csaReduce on k literal/constant words, k ≤ 9: value, depth bound, fan-in
def wordsK (k : ℕ) : List (List (TreeCircuit 6)) :=
  (List.range k).map fun i => [v ⟨i % 6, by omega⟩, .const (i % 2 == 0), .lit ⟨(i + 1) % 6, by omega⟩]
#eval tally ((List.range 10).flatMap fun k => (assigns 6).map fun x =>
  val x (csaReduce (wordsK k)).1 + val x (csaReduce (wordsK k)).2 == ((wordsK k).map (val x)).sum)
#eval tally ((List.range 10).map fun k =>
  decide (TreeCircuit.maxDepth ((csaReduce (wordsK k)).1 ++ (csaReduce (wordsK k)).2) ≤
    max 1 (TreeCircuit.maxDepth (wordsK k).flatten) + 4 * csaLevels (wordsK k).length) &&
  decide (TreeCircuit.maxFaninL ((csaReduce (wordsK k)).1 ++ (csaReduce (wordsK k)).2) ≤ 2))
#eval (List.range 10).map fun k =>
  (k, TreeCircuit.maxDepth ((csaReduce (wordsK k)).1 ++ (csaReduce (wordsK k)).2), csaLevels k)

/-! ## 4. F6 closed form `csaLevels k ≤ 2 ⌈log₂ k⌉` -/

/-- structural surrogate of `Nat.clog 2` -/
def clogS (k : ℕ) : ℕ := if k ≤ 1 then 0 else Nat.log2 (k - 1) + 1

#eval tally ((List.range 5000).map fun k => clogS k == Nat.clog 2 k)
example : ∀ k < 2000, csaLevels k ≤ 2 * clogS k := by decide +kernel
#eval tally ((List.range 100000).map fun k => decide (csaLevels k ≤ 2 * Nat.clog 2 k))
example : csaLevels 3 = 1 ∧ csaLevels 4 = 2 ∧ csaLevels 9 = 4 ∧ csaLevels 100 = 10 := by decide

/-! ## 5. F7 carry-out against `carryBit`, F8 comparison with a constant -/

#eval tally (words.flatMap fun U => words.flatMap fun W => (List.range 6).map fun b =>
  (carryOut U W b).eval x0 == carryBit (bitAt x0 U) (bitAt x0 W) b)
#eval tally (words.flatMap fun U => words.flatMap fun W => (List.range 6).filterMap fun b =>
  if U.length ≤ b ∧ W.length ≤ b then
    some ((carryOut U W b).eval x0 == decide (2 ^ b ≤ val x0 U + val x0 W)) else none)
#eval tally (words.flatMap fun U => words.flatMap fun W => (List.range 6).map fun b =>
  decide ((carryOut U W b).depth ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) + 2 * Nat.clog 2 b + 3)
  && decide ((carryOut U W b).maxFanin ≤ 2))
#eval tally (words.flatMap fun U => words.flatMap fun W => (List.range 20).map fun c =>
  (geConst U W c).eval x0 == decide (c ≤ val x0 U + val x0 W))
#eval tally (words.flatMap fun U => words.flatMap fun W => (List.range 20).map fun c =>
  decide ((geConst U W c).depth ≤
    max 1 (TreeCircuit.maxDepth (U ++ W)) + 2 * Nat.clog 2 (max U.length W.length + 1) + 7)
  && decide ((geConst U W c).maxFanin ≤ 2))
-- carry-out and comparison on literal words (all 64 assignments)
#eval tally ((assigns 6).flatMap fun x => (List.range 6).map fun b =>
  (carryOut LA LC b).eval x == carryBit (bitAt x LA) (bitAt x LC) b)
#eval tally ((assigns 6).flatMap fun x => (List.range 16).map fun c =>
  (geConst LA LC c).eval x == decide (c ≤ val x LA + val x LC))

/-! ## 6. F9–F10: the modular interval sum, exhaustively for 2 ≤ q ≤ 7, M ≤ 3 -/

/-- all coefficient vectors `a : Fin M → ℕ` with `a i < q` -/
def coeffs (M q : ℕ) : List (Fin M → ℕ) :=
  (List.range (q ^ M)).map fun m i => m / q ^ i.val % q

/-- failures of F9 with `lo ≤ hi ≤ q` (r3's hypotheses), and the number of checks -/
def checkF9 (M q : ℕ) : List Bool :=
  (coeffs M q).flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (hi + 1)).flatMap fun lo =>
      let F := modSumInterval a q lo hi
      (assigns M).map fun x =>
        F.eval x == decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)

/-- the same equation for `hi < lo ≤ q` (outside r3's hypothesis `lo ≤ hi`) -/
def checkF9rev (M q : ℕ) : List Bool :=
  (coeffs M q).flatMap fun a => (List.range (q + 1)).flatMap fun lo =>
    (List.range lo).flatMap fun hi =>
      let F := modSumInterval a q lo hi
      (assigns M).map fun x =>
        F.eval x == decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)

/-- F10 on every built formula: depth ≤ modSumDepth, fan-in ≤ 2 -/
def checkF10 (M q : ℕ) : List Bool :=
  (coeffs M q).flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (q + 1)).map fun lo =>
      let F := modSumInterval a q lo hi
      decide (F.depth ≤ modSumDepth M q) && decide (F.maxFanin ≤ 2)

#eval (List.range 4).flatMap fun M => (List.range' 2 6).map fun q => (M, q, tally (checkF9 M q))
#eval (List.range 4).flatMap fun M => (List.range' 2 6).map fun q =>
  (M, q, tally (checkF9rev M q))
#eval (List.range 4).flatMap fun M => (List.range' 2 6).map fun q => (M, q, tally (checkF10 M q))
-- q = 0, 1 edge cases (M = 0 forced for q = 0 by a i < q)
#eval (tally (checkF9 0 0), tally (checkF9 0 1), tally (checkF9 2 1), tally (checkF9 3 1))
-- the hypothesis `hi ≤ q` is needed: a counterexample without it (q = 4, lo = 5, hi = 6, x = 1)
#eval (modSumInterval (M := 2) ![3, 2] 4 5 6).eval ![true, true]
-- the hypothesis `a i < q` is needed: a counterexample without it (q = 3, a = (5), x = 1, [2,3))
#eval ((modSumInterval (M := 1) ![5] 3 2 3).eval ![true], decide (2 ≤ 5 % 3 ∧ 5 % 3 < 3))
-- actual depths against the bound, larger instances
#eval [(1, 3), (3, 7), (5, 17), (8, 31), (12, 61)].map fun (M, q) =>
  (M, q, (modSumInterval (M := M) (fun i => (7 * i.val + 3) % q) q (q / 4) (3 * q / 4)).depth,
    modSumDepth M q)

/-! ## 7. F10 closed form numerically -/

#eval tally ((List.range 300).flatMap fun M => (List.range 300).map fun q =>
  decide (modSumDepth M q ≤
    9 * Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 3) + 21))
-- slack of the closed form (minimum over the range) and the tighter form
#eval ((List.range 300).flatMap fun M => (List.range 300).map fun q =>
  (9 * Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 3) + 21) - modSumDepth M q).min?
#eval tally ((List.range 300).flatMap fun M => (List.range 300).map fun q =>
  decide (modSumDepth M q ≤
    9 * Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 1) + 10))
-- larger M, q on a sparse grid
#eval tally ((List.range 60).flatMap fun i => (List.range 60).map fun j =>
  let M := 37 * i * i + i
  let q := 2 ^ j + 3 * j
  decide (modSumDepth M q ≤
    9 * Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 3) + 21))

end P10
