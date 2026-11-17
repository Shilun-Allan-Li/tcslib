# lead duplication searches (U5 NC1, U11 ModSum), 2026-11-17T11:29:14Z
## grep -rn 'ne_one\b' TCSlib/Complexity/BranchingPrograms TCSlib/Complexity/CircuitComplexity
TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean:170:theorem shiftPrefix_ne_one {v : ℕ} : shiftPrefix n v ≠ n + 1 := shiftPrefix_ne (by omega)
TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean:208:    simp [strictGate, DAGGate.Strict, hinj.eq_iff, hnd, shiftPrefix_ne_one, shiftPrefix_ne_two]
## grep -rn '≠ 1' TCSlib/Complexity/BranchingPrograms TCSlib/Complexity/CircuitComplexity
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean:271:        if k = .not ∧ c ≠ 1 then false
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean:274:      by_cases h : k = .not ∧ c ≠ 1
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean:278:    have hc1 : (c ≠ 1) ↔ pre.length ≠ 1 := by
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean:285:      by_cases hk : k = .not ∧ c ≠ 1
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean:300:        have hk' : ¬(k = .not ∧ c ≠ 1) := fun ⟨h1, h2⟩ => hc1.mp h2 (hk h1)
## grep -rn '≠ id' TCSlib/Complexity/BranchingPrograms TCSlib/Complexity/CircuitComplexity
TCSlib/Complexity/BranchingPrograms/NC1.lean:107:`isFiveCycle_sigma1`, `TreeCircuitFamily.mem_language_iff`, and `⇑sigma1 ≠ id` (a five-cycle
TCSlib/Complexity/BranchingPrograms/NC1.lean:116:  have hσ1 : (⇑sigma1 : Fin 5 → Fin 5) ≠ id := by
## grep -rn 'cycleType_eq_zero' TCSlib/Complexity/BranchingPrograms TCSlib/Complexity/CircuitComplexity
## grep -rn 'IsFiveCycle.*ne' TCSlib/Complexity/BranchingPrograms TCSlib/Complexity/CircuitComplexity
TCSlib/Complexity/BranchingPrograms/Barrington.lean:355:`List.formPerm [0, a, b, c, d]` (`∀ σ, IsFiveCycle σ → σ ∈ l`, kernel `decide +kernel`, about
## grep -rn 'prefixVal.*testBit\|testBit.*prefixVal' TCSlib
## grep -rn 'prefixVal.*take\|take.*prefixVal\|bitsVal.*take' TCSlib
TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean:401:    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP n)) ≤ n + 1 ∧
TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:88:    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP n)) ≤ n + 1
TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:107:        R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) ∧
TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:134:    · set pos := bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length))
TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:137:        have h1 := bitsVal_lt_two_pow ((w.drop (W N * (2 * s + 1))).take (wP x.length))
TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean:112:        (layR N R x.length s (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))).val) ∨
TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean:77:          (bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length)))).val) ∨
TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean:91:    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) = 1 ∧
## grep -rn 'maxDepth_le\|maxFaninL_le' TCSlib
TCSlib/Complexity/CircuitComplexity/Basic.lean:290:theorem TreeCircuit.maxFaninL_le_sumSize :
TCSlib/Complexity/CircuitComplexity/Basic.lean:296:      have h2 := TreeCircuit.maxFaninL_le_sumSize (fun d hd => h d (List.mem_cons_of_mem _ hd))
TCSlib/Complexity/CircuitComplexity/Basic.lean:306:      have h₂ := TreeCircuit.maxFaninL_le_sumSize ih
## grep -rn 'pow_log.*poly\|4 \^ (b' TCSlib
TCSlib/Cryptography/Asymptotic/UniversalLemmas.lean:265:(`Nat.pow_log_le_self`), and `⌊log₂ 0⌋ = 0`. Hence `n ≤ 2 (n − ⌊log₂ n⌋)`, the polynomial
TCSlib/Complexity/BranchingPrograms/NC1.lean:104:Length: `barrington_length_le` and `4 ^ (b·(log₂ n + 1)) ≤ 4 ^ b · (n + 1) ^ (2b)`
TCSlib/Complexity/BranchingPrograms/NC1.lean:137:  · -- polynomial length: `4 ^ (b·(log₂ n + 1)) ≤ 4 ^ b · (n + 1) ^ (2b)`
TCSlib/Complexity/BranchingPrograms/NC1.lean:151:        _ ≤ 4 ^ (b * (Nat.log 2 n + 1)) := Nat.pow_le_pow_right (by norm_num) hd
## Mathlib: grep -rn 'theorem cycleType_eq_zero' mathlib
.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Cycle/Basic.lean:228:theorem IsCycle.ne_one (h : IsCycle f) : f ≠ 1 := fun hf => by simp [hf, IsCycle] at h
.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Cycle/Type.lean:91:theorem cycleType_eq_zero {σ : Perm α} : σ.cycleType = 0 ↔ σ = 1 := by
