# Full final Yao B excerpts

## strict · error 1 · yaoCoins_eval · original line 283

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:325:82: error: Type mismatch
  rfl
has type
  ?m.23 = ?m.23
but is expected to have type
  (yaoCoins Y).eval n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n
```

## strict · error 2 · yaoHybrid · original line 591

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:633:83: error: Application type mismatch: The argument
  j
has type
  Fin ((Y.inB.mul PolyExpr.var).eval n)
but is expected to have type
  Fin (Y.inB.eval n * n)
in the application
  yaoCall Y n j
```

## strict · error 3 · yaoHybrid · original line 592

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:634:40: error: Application type mismatch: The argument
  j
has type
  Fin ((Y.inB.mul PolyExpr.var).eval n)
but is expected to have type
  Fin (Y.inB.eval n * n)
in the application
  yaoCall Y n j
```

## strict · error 4 · yaoHybrid · original line 593

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:635:41: error: Application type mismatch: The argument
  j
has type
  Fin ((Y.inB.mul PolyExpr.var).eval n)
but is expected to have type
  Fin (Y.inB.eval n * n)
in the application
  yaoCall Y n j
```

## strict · error 5 · yaoHybrid_callA · original line 599

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:641:37: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callA n xs r j
```

## strict · error 6 · yaoHybrid_callB · original line 607

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:649:37: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callB n ys r j
```

## strict · error 7 · yaoHybrid_answersB_getD · original line 718

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:760:69: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callA n xs rA j
```

## strict · error 8 · yaoHybrid_answersB_getD · original line 719

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:761:41: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callB n ys rB j
```

## strict · error 9 · yaoHybrid_answersB_getD · original line 725

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:767:71: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callA n xs rA j
```

## strict · error 10 · yaoHybrid_answersB_getD · original line 726

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:768:41: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callB n ys rB j
```

## strict · error 11 · yaoSeed_good_whp · original line 817

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:859:56: error: Application type mismatch: The argument
  G₁
has type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool
but is expected to have type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((PolyExpr.var.add PolyExpr.var).eval n) → Bool
in the application
  PRFOut (PolyExpr.var.add PolyExpr.var) G₁
```

## strict · error 12 · yaoHybrid_polyTime · original line 917

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:959:4: error: Tactic `apply` failed: could not unify the conclusion of `CallEquations.inputA_eq Y.inA Y.sizeBound n (Y.inB.eval n) x
  r`
  OTInputs.otInputA Y.inA Y.sizeBound
      (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑?j) true)))) =
    List.ofFn (?call ?j)
with the goal
  OTInputs.otInputA Y.inA Y.sizeBound
      (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
    List.ofFn fun i => (yaoHybrid Y E₁ E₂).callA n x r j (Fin.cast ⋯ i)

Note: The full type of `CallEquations.inputA_eq Y.inA Y.sizeBound n (Y.inB.eval n) x r` is
  ∀ (call : Fin (Y.inB.eval n * n) → Fin 2 → Bool),
    (∀ (i : Fin (Y.inB.eval n)) (t : Fin n) (c : Fin 2),
        call (finProdFinEquiv (i, t)) c =
          r.getD (((decide (↑c = 1)).toNat * Y.sizeBound.eval n + Y.inA.eval n + ↑i) * n + ↑t) false) →
      ∀ (j : Fin (Y.inB.eval n * n)),
        OTInputs.otInputA Y.inA Y.sizeBound
            (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
          List.ofFn (call j)

case refine_1
Y : YaoCircuit
E₁ E₂ : List Bool → List Bool
hE₁ : PolyTimeComputable E₁
hE₂ : PolyTimeComputable E₂
hAlice : (yaoAlice Y E₁ E₂).Efficient
hBob : (yaoBob Y E₁ E₂).Efficient
n : ℕ
x r : List Bool
j : Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
hlen : otFunctionality.inA.eval n = 2
⊢ OTInputs.otInputA Y.inA Y.sizeBound
      (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
    List.ofFn fun i => (yaoHybrid Y E₁ E₂).callA n x r j (Fin.cast ⋯ i)
```

## strict · error 13 · yaoHybrid_polyTime · original line 929

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:971:4: error: Tactic `apply` failed: could not unify the conclusion of `CallEquations.inputB_eq n (Y.inB.eval n) x r`
  OTInputs.otInputB (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑?j) true)))) =
    List.ofFn (?call ?j)
with the goal
  OTInputs.otInputB (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
    List.ofFn fun i => (yaoHybrid Y E₁ E₂).callB n x r j (Fin.cast ⋯ i)

Note: The full type of `CallEquations.inputB_eq n (Y.inB.eval n) x r` is
  ∀ (call : Fin (Y.inB.eval n * n) → Fin 1 → Bool),
    (∀ (i : Fin (Y.inB.eval n)) (t : Fin n) (c : Fin 1), call (finProdFinEquiv (i, t)) c = x.getD (↑i) false) →
      ∀ (j : Fin (Y.inB.eval n * n)),
        OTInputs.otInputB
            (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
          List.ofFn (call j)

case refine_2
Y : YaoCircuit
E₁ E₂ : List Bool → List Bool
hE₁ : PolyTimeComputable E₁
hE₂ : PolyTimeComputable E₂
hAlice : (yaoAlice Y E₁ E₂).Efficient
hBob : (yaoBob Y E₁ E₂).Efficient
n : ℕ
x r : List Bool
j : Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
hlen : otFunctionality.inB.eval n = 1
⊢ OTInputs.otInputB (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
    List.ofFn fun i => (yaoHybrid Y E₁ E₂).callB n x r j (Fin.cast ⋯ i)
```

## strict · error 14 · yaoHybrid_simulators · original line 995

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1037:35: error: Application type mismatch: The argument
  G₁
has type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool
but is expected to have type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((PolyExpr.var.add PolyExpr.var).eval n) → Bool
in the application
  PRFOut (PolyExpr.var.add PolyExpr.var) G₁
```

## strict · error 15 · yaoHybrid_simulators · original line 997

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1039:20: error: Type mismatch
  Fin.append (G₁ n s x) (G₂ n s x)
has type
  Fin (n + n + (PolyExpr.var.add innerLen).eval n) → Bool
but is expected to have type
  Fin (((PolyExpr.var.add PolyExpr.var).add (PolyExpr.var.add innerLen)).eval n) → Bool
```

## strict · error 16 · yaoHybrid_simulators · original line 1016

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1058:69: error: Application type mismatch: The argument
  Y.circ
has type
  (n : ℕ) → DAGCircuit (Y.inA.eval n + Y.inB.eval n)
but is expected to have type
  (n : ℕ) → DAGCircuit ((Y.inA.add Y.inB).eval n)
in the application
  FakeSimulatorFactory.exists_simulator E₁ E₂ hE₁ hE₂ Y.sizeBound (Y.inA.add Y.inB) Y.inA Y.inB Y.outLen gen hgen Y.circ
```

## strict · error 17 · yaoHybrid_simulators · original line 1020

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1062:29: error: Type mismatch
  Nat.le_refl (Y.inA.eval n + Y.inB.eval n)
has type
  Y.inA.eval n + Y.inB.eval n ≤ Y.inA.eval n + Y.inB.eval n
but is expected to have type
  Y.inA.eval n + Y.inB.eval n ≤ (Y.inA.add Y.inB).eval n
```

## strict · error 18 · yaoHybrid_simulators · original line 1021

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1063:12: error: unsolved goals
case h
Y : YaoCircuit
E₁ E₂ : List Bool → List Bool
G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool
G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((PolyExpr.var.add innerLen).eval n) → Bool
hGE₁ : ∀ (n : ℕ) (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)
hGE₂ : ∀ (n : ℕ) (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)
hE₁ : PolyTimeComputable E₁
hE₂ : PolyTimeComputable E₂
hG₁ : PRFOut (PolyExpr.var.add PolyExpr.var) sorry
hG₂ : PRFOut (PolyExpr.var.add innerLen) G₂
hG₁₂ : PRFOut ((PolyExpr.var.add PolyExpr.var).add (PolyExpr.var.add innerLen)) fun n s x => sorry
hFan : ∀ (n : ℕ) (i : Fin (Y.circ n).gates.length), (Y.circ n).gates[↑i].args.length ≤ 2
hSeedK :
  ∀ (n : ℕ) (r : List Bool) (v : Fin (Y.circ n).size) (b : Bool),
    (yaoSeed Y n r).1 v b = readBits r ((b.toNat * Y.sizeBound.eval n + ↑v) * n) n
hSeedR₀ :
  ∀ (n : ℕ) (q : List Bool) (i : Fin (Y.circ n).gates.length) (a : Fin (Y.circ n).gates[i].args.length → Bool),
    ((yaoSeed Y n q).2.1 i a).1 =
      (readBits q (2 * Y.sizeBound.eval n * n + (4 * ↑i + assignIdx a) * (2 * n)) n,
          readBits q (2 * Y.sizeBound.eval n * n + (4 * ↑i + assignIdx a) * (2 * n) + n) n).1
hSeedR₁ :
  ∀ (n : ℕ) (q : List Bool) (i : Fin (Y.circ n).gates.length) (a : Fin (Y.circ n).gates[i].args.length → Bool),
    ((yaoSeed Y n q).2.1 i a).2 =
      (readBits q (2 * Y.sizeBound.eval n * n + (4 * ↑i + assignIdx a) * (2 * n)) n,
          readBits q (2 * Y.sizeBound.eval n * n + (4 * ↑i + assignIdx a) * (2 * n) + n) n).2
gen : List Bool → List Bool
hgen : PolyTimeComputable gen
hgenEq : ∀ (n : ℕ), gen (List.replicate n true) = encodeCircuit (Y.circ n) (Y.outs n)
n : ℕ
q : List Bool
w : ℕ
hw : w < (sorry n).size
b : Bool
t : Fin n
⊢ (if h : w < (sorry n).size then (sorry n q).1 ⟨w, h⟩ b else default) t =
    q.getD ((b.toNat * Y.sizeBound.eval n + w) * n + ↑t) false
```

## strict · error 19 · yaoHybrid_simulators · original line 1022

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1064:35: error: `simp` made no progress
```

## strict · error 20 · yaoHybrid_simulators · original line 1023

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1065:35: error: `simp` made no progress
```

## strict · error 21 · yaoHybrid_simulators · original line 1025

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1067:23: error: `simp` made no progress
```

## strict · error 22 · yaoHybrid_simulators · original line 1068

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1110:20: error: Type mismatch
  Fin.append (G₁ n s x) (G₂ n s x)
has type
  Fin (n + n + (PolyExpr.var.add innerLen).eval n) → Bool
but is expected to have type
  Fin (((PolyExpr.var.add PolyExpr.var).add (PolyExpr.var.add innerLen)).eval n) → Bool
```

## strict · error 23 · yaoHybrid_hbcSecure · original line 1142

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1184:35: error: Application type mismatch: The argument
  G₁
has type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool
but is expected to have type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((PolyExpr.var.add PolyExpr.var).eval n) → Bool
in the application
  PRFOut (PolyExpr.var.add PolyExpr.var) G₁
```

## strict · error 24 · yaoHybrid_hbcSecure · original line 1144

```text
evidence/seals/final-frozen-files/final/Yao_B_strict.lean:1186:20: error: Type mismatch
  Fin.append (G₁ n s x) (G₂ n s x)
has type
  Fin (n + n + (PolyExpr.var.add innerLen).eval n) → Bool
but is expected to have type
  Fin (((PolyExpr.var.add PolyExpr.var).add (PolyExpr.var.add innerLen)).eval n) → Bool
```

## coe · error 1 · yaoCoins_eval · original line 283

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:325:82: error: Type mismatch
  rfl
has type
  ?m.23 = ?m.23
but is expected to have type
  (yaoCoins Y).eval n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n
```

## coe · error 2 · yaoHybrid · original line 591

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:633:83: error: Application type mismatch: The argument
  j
has type
  Fin ((Y.inB.mul PolyExpr.var).eval n)
but is expected to have type
  Fin (Y.inB.eval n * n)
in the application
  yaoCall Y n j
```

## coe · error 3 · yaoHybrid · original line 592

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:634:40: error: Application type mismatch: The argument
  j
has type
  Fin ((Y.inB.mul PolyExpr.var).eval n)
but is expected to have type
  Fin (Y.inB.eval n * n)
in the application
  yaoCall Y n j
```

## coe · error 4 · yaoHybrid · original line 593

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:635:41: error: Application type mismatch: The argument
  j
has type
  Fin ((Y.inB.mul PolyExpr.var).eval n)
but is expected to have type
  Fin (Y.inB.eval n * n)
in the application
  yaoCall Y n j
```

## coe · error 5 · yaoHybrid_callA · original line 599

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:641:37: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callA n xs r j
```

## coe · error 6 · yaoHybrid_callB · original line 607

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:649:37: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callB n ys r j
```

## coe · error 7 · yaoHybrid_answersB_getD · original line 718

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:760:69: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callA n xs rA j
```

## coe · error 8 · yaoHybrid_answersB_getD · original line 719

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:761:41: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callB n ys rB j
```

## coe · error 9 · yaoHybrid_answersB_getD · original line 725

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:767:71: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callA n xs rA j
```

## coe · error 10 · yaoHybrid_answersB_getD · original line 726

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:768:41: error: Application type mismatch: The argument
  j
has type
  Fin (Y.inB.eval n * n)
but is expected to have type
  Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
in the application
  (yaoHybrid Y E₁ E₂).callB n ys rB j
```

## coe · error 11 · yaoSeed_good_whp · original line 817

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:859:56: error: Application type mismatch: The argument
  G₁
has type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool
but is expected to have type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((PolyExpr.var.add PolyExpr.var).eval n) → Bool
in the application
  PRFOut (PolyExpr.var.add PolyExpr.var) G₁
```

## coe · error 12 · yaoHybrid_polyTime · original line 917

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:959:4: error: Tactic `apply` failed: could not unify the conclusion of `CallEquations.inputA_eq Y.inA Y.sizeBound n (Y.inB.eval n) x
  r`
  OTInputs.otInputA Y.inA Y.sizeBound
      (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑?j) true)))) =
    List.ofFn (?call ?j)
with the goal
  OTInputs.otInputA Y.inA Y.sizeBound
      (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
    List.ofFn fun i => (yaoHybrid Y E₁ E₂).callA n x r j (Fin.cast ⋯ i)

Note: The full type of `CallEquations.inputA_eq Y.inA Y.sizeBound n (Y.inB.eval n) x r` is
  ∀ (call : Fin (Y.inB.eval n * n) → Fin 2 → Bool),
    (∀ (i : Fin (Y.inB.eval n)) (t : Fin n) (c : Fin 2),
        call (finProdFinEquiv (i, t)) c =
          r.getD (((decide (↑c = 1)).toNat * Y.sizeBound.eval n + Y.inA.eval n + ↑i) * n + ↑t) false) →
      ∀ (j : Fin (Y.inB.eval n * n)),
        OTInputs.otInputA Y.inA Y.sizeBound
            (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
          List.ofFn (call j)

case refine_1
Y : YaoCircuit
E₁ E₂ : List Bool → List Bool
hE₁ : PolyTimeComputable E₁
hE₂ : PolyTimeComputable E₂
hAlice : (yaoAlice Y E₁ E₂).Efficient
hBob : (yaoBob Y E₁ E₂).Efficient
n : ℕ
x r : List Bool
j : Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
hlen : otFunctionality.inA.eval n = 2
⊢ OTInputs.otInputA Y.inA Y.sizeBound
      (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
    List.ofFn fun i => (yaoHybrid Y E₁ E₂).callA n x r j (Fin.cast ⋯ i)
```

## coe · error 13 · yaoHybrid_polyTime · original line 929

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:971:4: error: Tactic `apply` failed: could not unify the conclusion of `CallEquations.inputB_eq n (Y.inB.eval n) x r`
  OTInputs.otInputB (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑?j) true)))) =
    List.ofFn (?call ?j)
with the goal
  OTInputs.otInputB (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
    List.ofFn fun i => (yaoHybrid Y E₁ E₂).callB n x r j (Fin.cast ⋯ i)

Note: The full type of `CallEquations.inputB_eq n (Y.inB.eval n) x r` is
  ∀ (call : Fin (Y.inB.eval n * n) → Fin 1 → Bool),
    (∀ (i : Fin (Y.inB.eval n)) (t : Fin n) (c : Fin 1), call (finProdFinEquiv (i, t)) c = x.getD (↑i) false) →
      ∀ (j : Fin (Y.inB.eval n * n)),
        OTInputs.otInputB
            (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
          List.ofFn (call j)

case refine_2
Y : YaoCircuit
E₁ E₂ : List Bool → List Bool
hE₁ : PolyTimeComputable E₁
hE₂ : PolyTimeComputable E₂
hAlice : (yaoAlice Y E₁ E₂).Efficient
hBob : (yaoBob Y E₁ E₂).Efficient
n : ℕ
x r : List Bool
j : Fin ((yaoHybrid Y E₁ E₂).calls.eval n)
hlen : otFunctionality.inB.eval n = 1
⊢ OTInputs.otInputB (pairEncode (List.replicate n true) (pairEncode x (pairEncode r (List.replicate (↑j) true)))) =
    List.ofFn fun i => (yaoHybrid Y E₁ E₂).callB n x r j (Fin.cast ⋯ i)
```

## coe · error 14 · yaoHybrid_simulators · original line 995

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1037:35: error: Application type mismatch: The argument
  G₁
has type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool
but is expected to have type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((PolyExpr.var.add PolyExpr.var).eval n) → Bool
in the application
  PRFOut (PolyExpr.var.add PolyExpr.var) G₁
```

## coe · error 15 · yaoHybrid_simulators · original line 997

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1039:20: error: Type mismatch
  Fin.append (G₁ n s x) (G₂ n s x)
has type
  Fin (n + n + (PolyExpr.var.add innerLen).eval n) → Bool
but is expected to have type
  Fin (((PolyExpr.var.add PolyExpr.var).add (PolyExpr.var.add innerLen)).eval n) → Bool
```

## coe · error 16 · yaoHybrid_simulators · original line 1016

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1058:69: error: Application type mismatch: The argument
  Y.circ
has type
  (n : ℕ) → DAGCircuit (Y.inA.eval n + Y.inB.eval n)
but is expected to have type
  (n : ℕ) → DAGCircuit ((Y.inA.add Y.inB).eval n)
in the application
  FakeSimulatorFactory.exists_simulator E₁ E₂ hE₁ hE₂ Y.sizeBound (Y.inA.add Y.inB) Y.inA Y.inB Y.outLen gen hgen Y.circ
```

## coe · error 17 · yaoHybrid_simulators · original line 1020

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1062:29: error: Type mismatch
  Nat.le_refl (Y.inA.eval n + Y.inB.eval n)
has type
  Y.inA.eval n + Y.inB.eval n ≤ Y.inA.eval n + Y.inB.eval n
but is expected to have type
  Y.inA.eval n + Y.inB.eval n ≤ (Y.inA.add Y.inB).eval n
```

## coe · error 18 · yaoHybrid_simulators · original line 1021

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1063:12: error: unsolved goals
case h
Y : YaoCircuit
E₁ E₂ : List Bool → List Bool
G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool
G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((PolyExpr.var.add innerLen).eval n) → Bool
hGE₁ : ∀ (n : ℕ) (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)
hGE₂ : ∀ (n : ℕ) (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)
hE₁ : PolyTimeComputable E₁
hE₂ : PolyTimeComputable E₂
hG₁ : PRFOut (PolyExpr.var.add PolyExpr.var) sorry
hG₂ : PRFOut (PolyExpr.var.add innerLen) G₂
hG₁₂ : PRFOut ((PolyExpr.var.add PolyExpr.var).add (PolyExpr.var.add innerLen)) fun n s x => sorry
hFan : ∀ (n : ℕ) (i : Fin (Y.circ n).gates.length), (Y.circ n).gates[↑i].args.length ≤ 2
hSeedK :
  ∀ (n : ℕ) (r : List Bool) (v : Fin (Y.circ n).size) (b : Bool),
    (yaoSeed Y n r).1 v b = readBits r ((b.toNat * Y.sizeBound.eval n + ↑v) * n) n
hSeedR₀ :
  ∀ (n : ℕ) (q : List Bool) (i : Fin (Y.circ n).gates.length) (a : Fin (Y.circ n).gates[i].args.length → Bool),
    ((yaoSeed Y n q).2.1 i a).1 =
      (readBits q (2 * Y.sizeBound.eval n * n + (4 * ↑i + assignIdx a) * (2 * n)) n,
          readBits q (2 * Y.sizeBound.eval n * n + (4 * ↑i + assignIdx a) * (2 * n) + n) n).1
hSeedR₁ :
  ∀ (n : ℕ) (q : List Bool) (i : Fin (Y.circ n).gates.length) (a : Fin (Y.circ n).gates[i].args.length → Bool),
    ((yaoSeed Y n q).2.1 i a).2 =
      (readBits q (2 * Y.sizeBound.eval n * n + (4 * ↑i + assignIdx a) * (2 * n)) n,
          readBits q (2 * Y.sizeBound.eval n * n + (4 * ↑i + assignIdx a) * (2 * n) + n) n).2
gen : List Bool → List Bool
hgen : PolyTimeComputable gen
hgenEq : ∀ (n : ℕ), gen (List.replicate n true) = encodeCircuit (Y.circ n) (Y.outs n)
n : ℕ
q : List Bool
w : ℕ
hw : w < (sorry n).size
b : Bool
t : Fin n
⊢ (if h : w < (sorry n).size then (sorry n q).1 ⟨w, h⟩ b else default) t =
    q.getD ((b.toNat * Y.sizeBound.eval n + w) * n + ↑t) false
```

## coe · error 19 · yaoHybrid_simulators · original line 1022

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1064:35: error: `simp` made no progress
```

## coe · error 20 · yaoHybrid_simulators · original line 1023

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1065:35: error: `simp` made no progress
```

## coe · error 21 · yaoHybrid_simulators · original line 1025

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1067:23: error: `simp` made no progress
```

## coe · error 22 · yaoHybrid_simulators · original line 1068

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1110:20: error: Type mismatch
  Fin.append (G₁ n s x) (G₂ n s x)
has type
  Fin (n + n + (PolyExpr.var.add innerLen).eval n) → Bool
but is expected to have type
  Fin (((PolyExpr.var.add PolyExpr.var).add (PolyExpr.var.add innerLen)).eval n) → Bool
```

## coe · error 23 · yaoHybrid_hbcSecure · original line 1142

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1184:35: error: Application type mismatch: The argument
  G₁
has type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool
but is expected to have type
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((PolyExpr.var.add PolyExpr.var).eval n) → Bool
in the application
  PRFOut (PolyExpr.var.add PolyExpr.var) G₁
```

## coe · error 24 · yaoHybrid_hbcSecure · original line 1144

```text
evidence/seals/final-frozen-files/final/Yao_B_coe.lean:1186:20: error: Type mismatch
  Fin.append (G₁ n s x) (G₂ n s x)
has type
  Fin (n + n + (PolyExpr.var.add innerLen).eval n) → Bool
but is expected to have type
  Fin (((PolyExpr.var.add PolyExpr.var).add (PolyExpr.var.add innerLen)).eval n) → Bool
```
