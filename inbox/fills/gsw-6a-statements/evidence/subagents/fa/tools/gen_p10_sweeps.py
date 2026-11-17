"""Generate the small P10 sweep probes (each Lean run well under two minutes)."""
import sys
out = sys.argv[1]
HEAD = '''import TCSlib.Complexity.CircuitComplexity.FormulaArith
import Mathlib.Algebra.BigOperators.Fin

/-!
# Probe {name} (part of P10, brief check 7)

{title}

Closed Booleans computed by `#eval` (`TreeCircuit.eval`/`depth`/`maxFanin` and `Nat.clog` are
well-founded and not kernel-reducible); each entry prints `(failures, cases)`, failures expected
`0`.  No `native_decide`.
-/

open BoolCircuit BoolCircuit.FormulaArith

namespace {name}

def assigns (n : ℕ) : List (Fin n → Bool) :=
  (List.range (2 ^ n)).map fun m i => m.testBit i
def tally (l : List Bool) : ℕ × ℕ := (l.countP (· = false), l.length)

/-- all coefficient vectors `a : Fin M → ℕ` with `a i < q`, numbered `m < q ^ M` -/
def coeffs (M q : ℕ) : List (Fin M → ℕ) :=
  (List.range (q ^ M)).map fun m i => m / q ^ i.val % q

/-- the coefficient vectors numbered `m ∈ [s, s + k)` -/
def coeffsPart (M q s k : ℕ) : List (Fin M → ℕ) :=
  (List.range' s k).map fun m i => m / q ^ i.val % q

/-- F9 by `TreeCircuit.eval`, for `lo ≤ hi ≤ q` (r3's hypotheses) -/
def checkF9 (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (hi + 1)).flatMap fun lo =>
      let F := modSumInterval a q lo hi
      (assigns M).map fun x =>
        F.eval x == decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)

/-- the same equation for `hi < lo ≤ q` (outside r3's hypothesis `lo ≤ hi`) -/
def checkF9rev (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun lo =>
    (List.range lo).flatMap fun hi =>
      let F := modSumInterval a q lo hi
      (assigns M).map fun x =>
        F.eval x == decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)

/-- F10 on every built formula (all `lo, hi ≤ q`): depth `≤ modSumDepth M q`, fan-in `≤ 2` -/
def checkF10 (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (q + 1)).map fun lo =>
      let F := modSumInterval a q lo hi
      decide (F.depth ≤ modSumDepth M q) && decide (F.maxFanin ≤ 2)

/-- bit-parallel evaluation on all `2 ^ M` assignments at once: bit `m` of the result is the
value under `fun i => m.testBit i` (the order of `assigns`).  Probe-only, cross-checked against
`TreeCircuit.eval` by `checkMask` in the same file. -/
partial def evalMask (M : ℕ) : TreeCircuit M → ℕ
  | .lit l =>
      let mk := ((List.range (2 ^ M)).filter fun m => m.testBit l.idx.val).foldl
        (fun acc m => acc ||| 2 ^ m) 0
      if l.sign then mk else (2 ^ 2 ^ M - 1) ^^^ mk
  | .node true cs => cs.foldl (fun acc c => acc &&& evalMask M c) (2 ^ 2 ^ M - 1)
  | .node false cs => cs.foldl (fun acc c => acc ||| evalMask M c) 0

/-- the expected value of F9's right side, as a mask over the assignments -/
def rhsMask (M q lo hi : ℕ) (a : Fin M → ℕ) : ℕ :=
  ((List.range (2 ^ M)).filter fun m =>
    decide (lo ≤ (∑ i, (m.testBit i.val).toNat * a i) % q ∧
      (∑ i, (m.testBit i.val).toNat * a i) % q < hi)).foldl (fun acc m => acc ||| 2 ^ m) 0

/-- F9 by the bit-parallel evaluator, for `lo ≤ hi ≤ q` -/
def checkF9mask (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (hi + 1)).map fun lo =>
      evalMask M (modSumInterval a q lo hi) == rhsMask M q lo hi a

/-- `evalMask` agrees with `TreeCircuit.eval` on the formulas of the given coefficients -/
def checkMask (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (hi + 1)).flatMap fun lo =>
      let F := modSumInterval a q lo hi
      (List.range (2 ^ M)).map fun m =>
        (evalMask M F).testBit m == F.eval fun i => m.testBit i.val

'''
files = {
 'P10b1': ("F9 (with and without `lo ≤ hi`) and F10, exhaustively: `M ≤ 1`, `2 ≤ q ≤ 7`; "
           "`M = 2`, `q ≤ 3`.",
  '''#eval (List.range 2).flatMap fun M => (List.range' 2 6).map fun q =>
  (M, q, tally (checkF9 M q (coeffs M q)), tally (checkF9rev M q (coeffs M q)),
    tally (checkF10 M q (coeffs M q)))
#eval (List.range' 2 2).map fun q => (2, q, tally (checkF9 2 q (coeffs 2 q)),
  tally (checkF9rev 2 q (coeffs 2 q)), tally (checkF10 2 q (coeffs 2 q)))
'''),
 'P10b2': ("F9 (with and without `lo ≤ hi`) and F10, exhaustively: `M = 2`, `4 ≤ q ≤ 7`.",
  '''#eval (List.range' 4 4).map fun q => (2, q, tally (checkF9 2 q (coeffs 2 q)),
  tally (checkF9rev 2 q (coeffs 2 q)), tally (checkF10 2 q (coeffs 2 q)))
'''),
 'P10b3': ("F9 (with and without `lo ≤ hi`) and F10, exhaustively: `M = 3`, `2 ≤ q ≤ 3`; "
           "edge cases `q ∈ {0, 1}`; the counterexamples without `hi ≤ q` and without `a i < q`.",
  '''#eval (List.range' 2 2).map fun q => (3, q, tally (checkF9 3 q (coeffs 3 q)),
  tally (checkF9rev 3 q (coeffs 3 q)), tally (checkF10 3 q (coeffs 3 q)))
-- q = 0 (forces M = 0) and q = 1
#eval (tally (checkF9 0 0 (coeffs 0 0)), tally (checkF9 0 1 (coeffs 0 1)),
  tally (checkF9 2 1 (coeffs 2 1)), tally (checkF9 3 1 (coeffs 3 1)))
-- `hi ≤ q` is needed: q = 4, a = (3, 2), [lo, hi) = [5, 6), x = (1, 1): S = 5, S % 4 = 1,
-- the right side is false; the formula (j = 0: 5 ≤ 5 < 6) is true
#eval ((modSumInterval (M := 2) (fun i => [3, 2].getD i.val 0) 4 5 6).eval fun _ => true,
  decide (5 ≤ 5 % 4 ∧ 5 % 4 < 6))
-- `a i < q` is needed: q = 3, a = (5), [2, 3), x = (1): 5 % 3 = 2 is in the interval, but the
-- masked constant keeps only ⌈log₂ 3⌉ = 2 bits of 5
#eval ((modSumInterval (M := 1) (fun _ => 5) 3 2 3).eval fun _ => true,
  decide (2 ≤ 5 % 3 ∧ 5 % 3 < 3))
'''),
 'P10b4': ("F9 (with and without `lo ≤ hi`) by `TreeCircuit.eval`, exhaustively: `M = 3`, `q = 4`.",
  '''#eval (3, 4, tally (checkF9 3 4 (coeffs 3 4)), tally (checkF9rev 3 4 (coeffs 3 4)))
'''),
 'P10b5': ("F10 (depth `≤ modSumDepth`, fan-in `≤ 2`) on every formula for `M = 3`, `q = 4`, and on "
           "all `lo, hi ≤ q` for 6 coefficient vectors (first and last three) each for `M = 3`, `5 ≤ q ≤ 7`; actual "
           "depths against the bound on larger instances.",
  '''#eval (3, 4, tally (checkF10 3 4 (coeffs 3 4)))
#eval (List.range' 5 3).map fun q => (3, q, tally (checkF10 3 q (coeffsPart 3 q 0 3 ++
  coeffsPart 3 q (q ^ 3 - 3) 3)))
#eval [(1, 3), (3, 7), (5, 17), (8, 31), (12, 61)].map fun (M, q) =>
  (M, q, (modSumInterval (M := M) (fun i => (7 * i.val + 3) % q) q (q / 4) (3 * q / 4)).depth,
    modSumDepth M q)
'''),
}
# M = 3, q = 5..7 by the bit-parallel evaluator, split into chunks of coefficient vectors
chunks = {5: [(0, 125)], 6: [(0, 108), (108, 108)], 7: [(0, 86), (86, 86), (172, 86), (258, 85)]}
k = 0
for q, parts in chunks.items():
    for (s, c) in parts:
        k += 1
        name = 'P10c%d' % k
        files[name] = (
          "F9 exhaustively by the bit-parallel evaluator `evalMask`: `M = 3`, `q = %d`, coefficient "
          "vectors numbered `%d ≤ m < %d` (of `%d`), all `lo ≤ hi ≤ q`, all 8 inputs; `evalMask` "
          "cross-checked against `TreeCircuit.eval` on the first two vectors of the chunk."
          % (q, s, s + c, q ** 3),
          '''#eval (3, %d, %d, tally (checkF9mask 3 %d (coeffsPart 3 %d %d %d)),
  tally (checkMask 3 %d (coeffsPart 3 %d %d 2)))
''' % (q, s, q, q, s, c, q, q, s))
for name, (title, body) in files.items():
    open('%s/%s_FormulaArith.lean' % (out, name), 'w').write(
        HEAD.format(name=name, title=title) + body + '\nend %s\n' % name)
print(' '.join(files))
