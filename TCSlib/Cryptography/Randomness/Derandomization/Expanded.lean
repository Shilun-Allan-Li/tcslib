/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Stretch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expanding a PRG to cover the verifier's coins

The polynomial stretch `a(s^d+1)^k+s+1` exceeds the seed length even at zero.
At the ceiling-root schedule it covers `a(n+1)^k` true random bits.

## Main results

* `TCSlib.Cryptography.Randomness.Derand.exists_secure_cover`: a secure
  generator with an FP evaluator and the required output-length envelope.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Lemma 80.5 and Theorem 180.1.
-/

namespace TCSlib.Cryptography.Randomness.Derand

open Complexity

/-- A secure PRG can cover every polynomial coin schedule at the integer-root
seed length: there are a secure `G` and an FP evaluator `F` such that
`F(ofFn s) = ofFn(G n s)` and
`polyLen a k n ≤ G.stretch.eval (ceilRoot d n)` for every `n`.
[PS10, Lemma 80.5 and Theorem 180.1]

**Proof sketch.** Truncate the given generator to one-bit stretch and use
`prg_expand` at the syntactic polynomial `a(s^d+1)^k+s+1`. The last two terms
make its expansion clause strict at every seed length. Extract the existing
FP evaluator through `PRG.secure_iff` and `PRG.easy_iff`. Finally
`n ≤ (ceilRoot d n)^d` gives the verifier's length bound by monotonicity of
fixed natural powers and multiplication. -/
theorem exists_secure_cover (hPRG : ∃ G : PRG, G.Secure) (a k d : ℕ) (hd : 0 < d) :
    ∃ (G : PRG) (F : List Bool → List Bool),
      G.Secure ∧ PolyTimeComputable F ∧
      (∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G.G n s)) ∧
      ∀ n, Randomized.polyLen a k n ≤ G.stretch.eval (ceilRoot d n) := by
  obtain ⟨G₀, hG₀⟩ := hPRG
  let p : PolyExpr := .add (.add
    (.mul (.const a) (.pow (.add (.pow .var d) (.const 1)) k)) .var) (.const 1)
  have hp (s : ℕ) : s < p.eval s := by
    simp only [p, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_pow, PolyExpr.eval_var]
    omega
  let G := PRG.expand G₀.truncate p hp
  have hG : G.Secure := prg_expand G₀.truncate p hp hG₀.truncate
  obtain ⟨F, hF, hFs⟩ := (PRG.easy_iff G).mp ((PRG.secure_iff G).mp hG).1
  refine ⟨G, F, hG, hF, hFs, fun n => ?_⟩
  rw [show G.stretch = p from PRG.expand_stretch G₀.truncate p hp]
  simp only [p, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_pow, PolyExpr.eval_var, Randomized.polyLen_eq]
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (le_ceilRoot_pow hd n) 1) k
  have hmul := Nat.mul_le_mul_left a hpow
  omega

end TCSlib.Cryptography.Randomness.Derand
