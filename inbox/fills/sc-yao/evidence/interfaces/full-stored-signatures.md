# Fully elaborated stored signatures

Proof source ref: `6e7ef601ad9a05d5e26d09f32eadb9c17a4a6cbc`. This file exports all 1490 complete Lean types,
including implicit section parameters and private/generated constants. The raw
authoritative output is `evidence/probe-runs/final-publication-all-stored-1/9fff4353dc8b__AllAxioms.log`; SHA256 `94c295e3a0a74bab0688b42e0fedfa8c67246bf2cbe295faf970bcb201d16b2b`.

These are elaborated type displays, rather than source-header lexer excerpts.

## `BoolCircuit.DAGCircuit`

```lean
BoolCircuit.DAGCircuit : ℕ → Type
```

## `BoolCircuit.DAGCircuit.IsFaninTwo`

```lean
BoolCircuit.DAGCircuit.IsFaninTwo : {n : ℕ} → BoolCircuit.DAGCircuit n → Prop
```

## `BoolCircuit.DAGCircuit.IsWellFormed`

```lean
BoolCircuit.DAGCircuit.IsWellFormed : {n : ℕ} → BoolCircuit.DAGCircuit n → Prop
```

## `BoolCircuit.DAGCircuit._sizeOf_1`

```lean
BoolCircuit.DAGCircuit._sizeOf_1 : {n : ℕ} → BoolCircuit.DAGCircuit n → ℕ
```

## `BoolCircuit.DAGCircuit._sizeOf_inst`

```lean
BoolCircuit.DAGCircuit._sizeOf_inst : (n : ℕ) → SizeOf (BoolCircuit.DAGCircuit n)
```

## `BoolCircuit.DAGCircuit.args_lt`

```lean
BoolCircuit.DAGCircuit.args_lt : ∀ {n : ℕ} (self : BoolCircuit.DAGCircuit n) (i : ℕ)
  (h : i < self.gates.length), ∀ a ∈ self.gates[i].args, a < n + i
```

## `BoolCircuit.DAGCircuit.casesOn`

```lean
BoolCircuit.DAGCircuit.casesOn : {n : ℕ} →
  {motive : BoolCircuit.DAGCircuit n → Sort u} →
    (t : BoolCircuit.DAGCircuit n) →
      ((gates : List BoolCircuit.DAGGate) →
          (output : ℕ) →
            (args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) →
              (output_lt : output < n + gates.length) →
                motive { gates := gates, output := output, args_lt := args_lt, output_lt := output_lt }) →
        motive t
```

## `BoolCircuit.DAGCircuit.ctorIdx`

```lean
BoolCircuit.DAGCircuit.ctorIdx : {n : ℕ} → BoolCircuit.DAGCircuit n → ℕ
```

## `BoolCircuit.DAGCircuit.depth`

```lean
BoolCircuit.DAGCircuit.depth : {n : ℕ} → BoolCircuit.DAGCircuit n → ℕ
```

## `BoolCircuit.DAGCircuit.depthAt`

```lean
BoolCircuit.DAGCircuit.depthAt : {n : ℕ} → BoolCircuit.DAGCircuit n → ℕ → ℕ
```

## `BoolCircuit.DAGCircuit.depthAt.eq_1`

```lean
BoolCircuit.DAGCircuit.depthAt.eq_1 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) (v : ℕ),
  C.depthAt v = C.depths.getD v 0
```

## `BoolCircuit.DAGCircuit.depthAt_gate`

```lean
BoolCircuit.DAGCircuit.depthAt_gate : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) {i : ℕ}
  (hi : i < C.gates.length), C.depthAt (n + i) = C.gates[i].depth C.depths
```

## `BoolCircuit.DAGCircuit.depthAt_input`

```lean
BoolCircuit.DAGCircuit.depthAt_input : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) {i : ℕ}, i < n → C.depthAt i = 0
```

## `BoolCircuit.DAGCircuit.depths`

```lean
BoolCircuit.DAGCircuit.depths : {n : ℕ} → BoolCircuit.DAGCircuit n → List ℕ
```

## `BoolCircuit.DAGCircuit.depths.eq_1`

```lean
BoolCircuit.DAGCircuit.depths.eq_1 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.depths = BoolCircuit.runWith BoolCircuit.DAGGate.depth C.gates (List.replicate n 0)
```

## `BoolCircuit.DAGCircuit.encode`

```lean
BoolCircuit.DAGCircuit.encode : {n : ℕ} → BoolCircuit.DAGCircuit n → List Bool
```

## `BoolCircuit.DAGCircuit.encode.eq_1`

```lean
BoolCircuit.DAGCircuit.encode.eq_1 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.encode =
    BoolCircuit.encodeNat n ++
      (BoolCircuit.encodeList BoolCircuit.DAGGate.encode C.gates ++ BoolCircuit.encodeNat C.output)
```

## `BoolCircuit.DAGCircuit.encode_injective`

```lean
BoolCircuit.DAGCircuit.encode_injective : ∀ (n : ℕ), Function.Injective BoolCircuit.DAGCircuit.encode
```

## `BoolCircuit.DAGCircuit.encode_parts`

```lean
BoolCircuit.DAGCircuit.encode_parts : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.encode =
    BoolCircuit.encodeNat n ++
      (BoolCircuit.encodeList BoolCircuit.DAGGate.encode C.gates ++ BoolCircuit.encodeNat C.output)
```

## `BoolCircuit.DAGCircuit.eq_of_encode_eq`

```lean
BoolCircuit.DAGCircuit.eq_of_encode_eq : ∀ {n₁ n₂ : ℕ} {C₁ : BoolCircuit.DAGCircuit n₁}
  {C₂ : BoolCircuit.DAGCircuit n₂}, C₁.encode = C₂.encode → n₁ = n₂ ∧ C₁.gates = C₂.gates ∧ C₁.output = C₂.output
```

## `BoolCircuit.DAGCircuit.eval`

```lean
BoolCircuit.DAGCircuit.eval : {n : ℕ} → BoolCircuit.DAGCircuit n → (Fin n → Bool) → Bool
```

## `BoolCircuit.DAGCircuit.eval.eq_1`

```lean
BoolCircuit.DAGCircuit.eval.eq_1 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) (x : Fin n → Bool),
  C.eval x = (C.values x).getD C.output false
```

## `BoolCircuit.DAGCircuit.eval_eq`

```lean
BoolCircuit.DAGCircuit.eval_eq : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) (x : Fin n → Bool),
  C.eval x = (C.values x).getD C.output false
```

## `BoolCircuit.DAGCircuit.gates`

```lean
BoolCircuit.DAGCircuit.gates : {n : ℕ} → BoolCircuit.DAGCircuit n → List BoolCircuit.DAGGate
```

## `BoolCircuit.DAGCircuit.isFaninTwo_iff`

```lean
BoolCircuit.DAGCircuit.isFaninTwo_iff : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.IsFaninTwo ↔
    (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = BoolCircuit.GateKind.not → g.args.length = 1)) ∧
      ∀ g ∈ C.gates, g.args.length ≤ 2
```

## `BoolCircuit.DAGCircuit.length_depths`

```lean
BoolCircuit.DAGCircuit.length_depths : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.depths.length = n + C.gates.length
```

## `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`

```lean
BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.IsFaninTwo → C.encode.length ≤ 12 * C.size ^ 2
```

## `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo._proof_1_2`

```lean
BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo._proof_1_2 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.output < n + C.gates.length → ¬1 ≤ n + C.gates.length → False
```

## `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo._proof_1_3`

```lean
BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo._proof_1_3 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  ∀ i < C.gates.length, ∀ a < n + i, ¬a + 1 ≤ n + C.gates.length → False
```

## `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo._proof_1_5`

```lean
BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo._proof_1_5 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  ¬C.gates.length ≤ n + C.gates.length → False
```

## `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo._proof_1_6`

```lean
BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo._proof_1_6 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  ¬n ≤ n + C.gates.length → False
```

## `BoolCircuit.DAGCircuit.length_values`

```lean
BoolCircuit.DAGCircuit.length_values : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) (x : Fin n → Bool),
  (C.values x).length = n + C.gates.length
```

## `BoolCircuit.DAGCircuit.mk`

```lean
BoolCircuit.DAGCircuit.mk : {n : ℕ} →
  (gates : List BoolCircuit.DAGGate) →
    (output : ℕ) →
      (∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) →
        output < n + gates.length → BoolCircuit.DAGCircuit n
```

## `BoolCircuit.DAGCircuit.mk._flat_ctor`

```lean
BoolCircuit.DAGCircuit.mk._flat_ctor : {n : ℕ} →
  (gates : List BoolCircuit.DAGGate) →
    (output : ℕ) →
      (∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) →
        output < n + gates.length → BoolCircuit.DAGCircuit n
```

## `BoolCircuit.DAGCircuit.mk.congr_simp`

```lean
BoolCircuit.DAGCircuit.mk.congr_simp : ∀ {n : ℕ} (gates gates_1 : List BoolCircuit.DAGGate)
  (e_gates : gates = gates_1) (output output_1 : ℕ) (e_output : output = output_1)
  (args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) (output_lt : output < n + gates.length),
  { gates := gates, output := output, args_lt := args_lt, output_lt := output_lt } =
    { gates := gates_1, output := output_1, args_lt := ⋯, output_lt := ⋯ }
```

## `BoolCircuit.DAGCircuit.mk.inj`

```lean
BoolCircuit.DAGCircuit.mk.inj : ∀ {n : ℕ} {gates : List BoolCircuit.DAGGate} {output : ℕ}
  {args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i} {output_lt : output < n + gates.length}
  {gates_1 : List BoolCircuit.DAGGate} {output_1 : ℕ}
  {args_lt_1 : ∀ (i : ℕ) (h : i < gates_1.length), ∀ a ∈ gates_1[i].args, a < n + i}
  {output_lt_1 : output_1 < n + gates_1.length},
  { gates := gates, output := output, args_lt := args_lt, output_lt := output_lt } =
      { gates := gates_1, output := output_1, args_lt := args_lt_1, output_lt := output_lt_1 } →
    gates = gates_1 ∧ output = output_1
```

## `BoolCircuit.DAGCircuit.mk.injEq`

```lean
BoolCircuit.DAGCircuit.mk.injEq : ∀ {n : ℕ} (gates : List BoolCircuit.DAGGate) (output : ℕ)
  (args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) (output_lt : output < n + gates.length)
  (gates_1 : List BoolCircuit.DAGGate) (output_1 : ℕ)
  (args_lt_1 : ∀ (i : ℕ) (h : i < gates_1.length), ∀ a ∈ gates_1[i].args, a < n + i)
  (output_lt_1 : output_1 < n + gates_1.length),
  ({ gates := gates, output := output, args_lt := args_lt, output_lt := output_lt } =
      { gates := gates_1, output := output_1, args_lt := args_lt_1, output_lt := output_lt_1 }) =
    (gates = gates_1 ∧ output = output_1)
```

## `BoolCircuit.DAGCircuit.mk.noConfusion`

```lean
BoolCircuit.DAGCircuit.mk.noConfusion : {n : ℕ} →
  (P : Sort u) →
    (gates : List BoolCircuit.DAGGate) →
      (output : ℕ) →
        (args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) →
          (output_lt : output < n + gates.length) →
            (gates' : List BoolCircuit.DAGGate) →
              (output' : ℕ) →
                (args_lt' : ∀ (i : ℕ) (h : i < gates'.length), ∀ a ∈ gates'[i].args, a < n + i) →
                  (output_lt' : output' < n + gates'.length) →
                    { gates := gates, output := output, args_lt := args_lt, output_lt := output_lt } =
                        { gates := gates', output := output', args_lt := args_lt', output_lt := output_lt' } →
                      (gates = gates' → output = output' → P) → P
```

## `BoolCircuit.DAGCircuit.mk.sizeOf_spec`

```lean
BoolCircuit.DAGCircuit.mk.sizeOf_spec : ∀ {n : ℕ} (gates : List BoolCircuit.DAGGate) (output : ℕ)
  (args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) (output_lt : output < n + gates.length),
  sizeOf { gates := gates, output := output, args_lt := args_lt, output_lt := output_lt } =
    1 + sizeOf gates + sizeOf output + sizeOf output_lt
```

## `BoolCircuit.DAGCircuit.noConfusion`

```lean
BoolCircuit.DAGCircuit.noConfusion : {n : ℕ} →
  {P : Sort u} → {x1 x2 : BoolCircuit.DAGCircuit n} → x1 = x2 → BoolCircuit.DAGCircuit.noConfusionType P x1 x2
```

## `BoolCircuit.DAGCircuit.noConfusionType`

```lean
BoolCircuit.DAGCircuit.noConfusionType : {n : ℕ} →
  Sort u → BoolCircuit.DAGCircuit n → BoolCircuit.DAGCircuit n → Sort u
```

## `BoolCircuit.DAGCircuit.output`

```lean
BoolCircuit.DAGCircuit.output : {n : ℕ} → BoolCircuit.DAGCircuit n → ℕ
```

## `BoolCircuit.DAGCircuit.output_lt`

```lean
BoolCircuit.DAGCircuit.output_lt : ∀ {n : ℕ} (self : BoolCircuit.DAGCircuit n),
  self.output < n + self.gates.length
```

## `BoolCircuit.DAGCircuit.rec`

```lean
BoolCircuit.DAGCircuit.rec : {n : ℕ} →
  {motive : BoolCircuit.DAGCircuit n → Sort u} →
    ((gates : List BoolCircuit.DAGGate) →
        (output : ℕ) →
          (args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) →
            (output_lt : output < n + gates.length) →
              motive { gates := gates, output := output, args_lt := args_lt, output_lt := output_lt }) →
      (t : BoolCircuit.DAGCircuit n) → motive t
```

## `BoolCircuit.DAGCircuit.recOn`

```lean
BoolCircuit.DAGCircuit.recOn : {n : ℕ} →
  {motive : BoolCircuit.DAGCircuit n → Sort u} →
    (t : BoolCircuit.DAGCircuit n) →
      ((gates : List BoolCircuit.DAGGate) →
          (output : ℕ) →
            (args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ gates[i].args, a < n + i) →
              (output_lt : output < n + gates.length) →
                motive { gates := gates, output := output, args_lt := args_lt, output_lt := output_lt }) →
        motive t
```

## `BoolCircuit.DAGCircuit.size`

```lean
BoolCircuit.DAGCircuit.size : {n : ℕ} → BoolCircuit.DAGCircuit n → ℕ
```

## `BoolCircuit.DAGCircuit.size_eq`

```lean
BoolCircuit.DAGCircuit.size_eq : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n), C.size = n + C.gates.length
```

## `BoolCircuit.DAGCircuit.size_le_length_encode`

```lean
BoolCircuit.DAGCircuit.size_le_length_encode : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.size ≤ C.encode.length
```

## `BoolCircuit.DAGCircuit.size_le_length_encode._proof_1_3`

```lean
BoolCircuit.DAGCircuit.size_le_length_encode._proof_1_3 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n),
  C.gates.length + 1 ≤ (BoolCircuit.encodeList BoolCircuit.DAGGate.encode C.gates).length →
    ¬n + C.gates.length ≤
          n + 1 + ((BoolCircuit.encodeList BoolCircuit.DAGGate.encode C.gates).length + (C.output + 1)) →
      False
```

## `BoolCircuit.DAGCircuit.values`

```lean
BoolCircuit.DAGCircuit.values : {n : ℕ} → BoolCircuit.DAGCircuit n → (Fin n → Bool) → List Bool
```

## `BoolCircuit.DAGCircuit.values.eq_1`

```lean
BoolCircuit.DAGCircuit.values.eq_1 : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) (x : Fin n → Bool),
  C.values x = BoolCircuit.runWith BoolCircuit.DAGGate.eval C.gates (List.ofFn x)
```

## `BoolCircuit.DAGCircuit.values_eq`

```lean
BoolCircuit.DAGCircuit.values_eq : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) (x : Fin n → Bool),
  C.values x = BoolCircuit.runWith BoolCircuit.DAGGate.eval C.gates (List.ofFn x)
```

## `BoolCircuit.DAGCircuit.values_getD_gate`

```lean
BoolCircuit.DAGCircuit.values_getD_gate : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) (x : Fin n → Bool) {i : ℕ}
  (hi : i < C.gates.length), (C.values x).getD (n + i) false = C.gates[i].eval (C.values x)
```

## `BoolCircuit.DAGCircuit.values_getD_input`

```lean
BoolCircuit.DAGCircuit.values_getD_input : ∀ {n : ℕ} (C : BoolCircuit.DAGCircuit n) (x : Fin n → Bool)
  (i : Fin n), (C.values x).getD (↑i) false = x i
```

## `BoolCircuit.DAGCircuitFamily`

```lean
BoolCircuit.DAGCircuitFamily : Type
```

## `BoolCircuit.DAGCircuitFamily.Accepts`

```lean
BoolCircuit.DAGCircuitFamily.Accepts : BoolCircuit.DAGCircuitFamily → List Bool → Prop
```

## `BoolCircuit.DAGCircuitFamily.HasFaninTwo`

```lean
BoolCircuit.DAGCircuitFamily.HasFaninTwo : BoolCircuit.DAGCircuitFamily → Prop
```

## `BoolCircuit.DAGCircuitFamily.HasFaninTwo.isWellFormed`

```lean
BoolCircuit.DAGCircuitFamily.HasFaninTwo.isWellFormed : ∀ {C : BoolCircuit.DAGCircuitFamily},
  C.HasFaninTwo → C.IsWellFormed
```

## `BoolCircuit.DAGCircuitFamily.HasPolylogDepth`

```lean
BoolCircuit.DAGCircuitFamily.HasPolylogDepth : BoolCircuit.DAGCircuitFamily → ℕ → Prop
```

## `BoolCircuit.DAGCircuitFamily.IsPUniform`

```lean
BoolCircuit.DAGCircuitFamily.IsPUniform : BoolCircuit.DAGCircuitFamily → Prop
```

## `BoolCircuit.DAGCircuitFamily.IsPUniform.isPolySize`

```lean
BoolCircuit.DAGCircuitFamily.IsPUniform.isPolySize : ∀ {C : BoolCircuit.DAGCircuitFamily},
  C.IsPUniform → C.IsPolySize
```

## `BoolCircuit.DAGCircuitFamily.IsPolySize`

```lean
BoolCircuit.DAGCircuitFamily.IsPolySize : BoolCircuit.DAGCircuitFamily → Prop
```

## `BoolCircuit.DAGCircuitFamily.IsWellFormed`

```lean
BoolCircuit.DAGCircuitFamily.IsWellFormed : BoolCircuit.DAGCircuitFamily → Prop
```

## `BoolCircuit.DAGCircuitFamily._sizeOf_1`

```lean
BoolCircuit.DAGCircuitFamily._sizeOf_1 : BoolCircuit.DAGCircuitFamily → ℕ
```

## `BoolCircuit.DAGCircuitFamily._sizeOf_inst`

```lean
BoolCircuit.DAGCircuitFamily._sizeOf_inst : SizeOf BoolCircuit.DAGCircuitFamily
```

## `BoolCircuit.DAGCircuitFamily.casesOn`

```lean
BoolCircuit.DAGCircuitFamily.casesOn : {motive : BoolCircuit.DAGCircuitFamily → Sort u} →
  (t : BoolCircuit.DAGCircuitFamily) →
    ((circuit : (n : ℕ) → BoolCircuit.DAGCircuit n) → motive { circuit := circuit }) → motive t
```

## `BoolCircuit.DAGCircuitFamily.circuit`

```lean
BoolCircuit.DAGCircuitFamily.circuit : BoolCircuit.DAGCircuitFamily → (n : ℕ) → BoolCircuit.DAGCircuit n
```

## `BoolCircuit.DAGCircuitFamily.ctorIdx`

```lean
BoolCircuit.DAGCircuitFamily.ctorIdx : BoolCircuit.DAGCircuitFamily → ℕ
```

## `BoolCircuit.DAGCircuitFamily.language`

```lean
BoolCircuit.DAGCircuitFamily.language : BoolCircuit.DAGCircuitFamily → Language Bool
```

## `BoolCircuit.DAGCircuitFamily.mem_language_iff`

```lean
BoolCircuit.DAGCircuitFamily.mem_language_iff : ∀ (C : BoolCircuit.DAGCircuitFamily) (w : List Bool),
  w ∈ C.language ↔ (C.circuit w.length).eval w.get = true
```

## `BoolCircuit.DAGCircuitFamily.mem_language_iff._simp_1`

```lean
BoolCircuit.DAGCircuitFamily.mem_language_iff._simp_1 : ∀ (C : BoolCircuit.DAGCircuitFamily) (w : List Bool),
  (w ∈ C.language) = ((C.circuit w.length).eval w.get = true)
```

## `BoolCircuit.DAGCircuitFamily.mk`

```lean
BoolCircuit.DAGCircuitFamily.mk : ((n : ℕ) → BoolCircuit.DAGCircuit n) → BoolCircuit.DAGCircuitFamily
```

## `BoolCircuit.DAGCircuitFamily.mk._flat_ctor`

```lean
BoolCircuit.DAGCircuitFamily.mk._flat_ctor : ((n : ℕ) → BoolCircuit.DAGCircuit n) → BoolCircuit.DAGCircuitFamily
```

## `BoolCircuit.DAGCircuitFamily.mk.inj`

```lean
BoolCircuit.DAGCircuitFamily.mk.inj : ∀ {circuit circuit_1 : (n : ℕ) → BoolCircuit.DAGCircuit n},
  { circuit := circuit } = { circuit := circuit_1 } → circuit = circuit_1
```

## `BoolCircuit.DAGCircuitFamily.mk.injEq`

```lean
BoolCircuit.DAGCircuitFamily.mk.injEq : ∀ (circuit circuit_1 : (n : ℕ) → BoolCircuit.DAGCircuit n),
  ({ circuit := circuit } = { circuit := circuit_1 }) = (circuit = circuit_1)
```

## `BoolCircuit.DAGCircuitFamily.mk.noConfusion`

```lean
BoolCircuit.DAGCircuitFamily.mk.noConfusion : (P : Sort u) →
  (circuit circuit' : (n : ℕ) → BoolCircuit.DAGCircuit n) →
    { circuit := circuit } = { circuit := circuit' } → (circuit = circuit' → P) → P
```

## `BoolCircuit.DAGCircuitFamily.mk.sizeOf_spec`

```lean
BoolCircuit.DAGCircuitFamily.mk.sizeOf_spec : ∀ (circuit : (n : ℕ) → BoolCircuit.DAGCircuit n),
  sizeOf { circuit := circuit } = 1
```

## `BoolCircuit.DAGCircuitFamily.noConfusion`

```lean
BoolCircuit.DAGCircuitFamily.noConfusion : {P : Sort u} →
  {x1 x2 : BoolCircuit.DAGCircuitFamily} → x1 = x2 → BoolCircuit.DAGCircuitFamily.noConfusionType P x1 x2
```

## `BoolCircuit.DAGCircuitFamily.noConfusionType`

```lean
BoolCircuit.DAGCircuitFamily.noConfusionType : Sort u →
  BoolCircuit.DAGCircuitFamily → BoolCircuit.DAGCircuitFamily → Sort u
```

## `BoolCircuit.DAGCircuitFamily.rec`

```lean
BoolCircuit.DAGCircuitFamily.rec : {motive : BoolCircuit.DAGCircuitFamily → Sort u} →
  ((circuit : (n : ℕ) → BoolCircuit.DAGCircuit n) → motive { circuit := circuit }) →
    (t : BoolCircuit.DAGCircuitFamily) → motive t
```

## `BoolCircuit.DAGCircuitFamily.recOn`

```lean
BoolCircuit.DAGCircuitFamily.recOn : {motive : BoolCircuit.DAGCircuitFamily → Sort u} →
  (t : BoolCircuit.DAGCircuitFamily) →
    ((circuit : (n : ℕ) → BoolCircuit.DAGCircuit n) → motive { circuit := circuit }) → motive t
```

## `BoolCircuit.DAGGate`

```lean
BoolCircuit.DAGGate : Type
```

## `BoolCircuit.DAGGate.FaninTwo`

```lean
BoolCircuit.DAGGate.FaninTwo : BoolCircuit.DAGGate → Prop
```

## `BoolCircuit.DAGGate.WellFormed`

```lean
BoolCircuit.DAGGate.WellFormed : BoolCircuit.DAGGate → Prop
```

## `BoolCircuit.DAGGate._sizeOf_1`

```lean
BoolCircuit.DAGGate._sizeOf_1 : BoolCircuit.DAGGate → ℕ
```

## `BoolCircuit.DAGGate._sizeOf_inst`

```lean
BoolCircuit.DAGGate._sizeOf_inst : SizeOf BoolCircuit.DAGGate
```

## `BoolCircuit.DAGGate.args`

```lean
BoolCircuit.DAGGate.args : BoolCircuit.DAGGate → List ℕ
```

## `BoolCircuit.DAGGate.casesOn`

```lean
BoolCircuit.DAGGate.casesOn : {motive : BoolCircuit.DAGGate → Sort u} →
  (t : BoolCircuit.DAGGate) →
    ((kind : BoolCircuit.GateKind) → (args : List ℕ) → motive { kind := kind, args := args }) → motive t
```

## `BoolCircuit.DAGGate.ctorIdx`

```lean
BoolCircuit.DAGGate.ctorIdx : BoolCircuit.DAGGate → ℕ
```

## `BoolCircuit.DAGGate.depth`

```lean
BoolCircuit.DAGGate.depth : BoolCircuit.DAGGate → List ℕ → ℕ
```

## `BoolCircuit.DAGGate.depth_congr`

```lean
BoolCircuit.DAGGate.depth_congr : ∀ (g : BoolCircuit.DAGGate) {ds ds' : List ℕ},
  (∀ a ∈ g.args, ds.getD a 0 = ds'.getD a 0) → g.depth ds = g.depth ds'
```

## `BoolCircuit.DAGGate.encode`

```lean
BoolCircuit.DAGGate.encode : BoolCircuit.DAGGate → List Bool
```

## `BoolCircuit.DAGGate.encode.eq_1`

```lean
BoolCircuit.DAGGate.encode.eq_1 : ∀ (g : BoolCircuit.DAGGate),
  g.encode = g.kind.encode ++ BoolCircuit.encodeList BoolCircuit.encodeNat g.args
```

## `BoolCircuit.DAGGate.encode_eq`

```lean
BoolCircuit.DAGGate.encode_eq : ∀ (g : BoolCircuit.DAGGate),
  g.encode = g.kind.encode ++ BoolCircuit.encodeList BoolCircuit.encodeNat g.args
```

## `BoolCircuit.DAGGate.eval`

```lean
BoolCircuit.DAGGate.eval : BoolCircuit.DAGGate → List Bool → Bool
```

## `BoolCircuit.DAGGate.eval.eq_1`

```lean
BoolCircuit.DAGGate.eval.eq_1 : ∀ (g : BoolCircuit.DAGGate) (vals : List Bool),
  g.eval vals =
    match g.kind with
    | BoolCircuit.GateKind.and => g.args.all fun a => vals.getD a false
    | BoolCircuit.GateKind.or => g.args.any fun a => vals.getD a false
    | BoolCircuit.GateKind.not => !g.args.all fun a => vals.getD a false
```

## `BoolCircuit.DAGGate.eval_congr`

```lean
BoolCircuit.DAGGate.eval_congr : ∀ (g : BoolCircuit.DAGGate) {vals vals' : List Bool},
  (∀ a ∈ g.args, vals.getD a false = vals'.getD a false) → g.eval vals = g.eval vals'
```

## `BoolCircuit.DAGGate.eval_eq`

```lean
BoolCircuit.DAGGate.eval_eq : ∀ (g : BoolCircuit.DAGGate) (vals : List Bool),
  g.eval vals =
    match g.kind with
    | BoolCircuit.GateKind.and => g.args.all fun a => vals.getD a false
    | BoolCircuit.GateKind.or => g.args.any fun a => vals.getD a false
    | BoolCircuit.GateKind.not => !g.args.all fun a => vals.getD a false
```

## `BoolCircuit.DAGGate.eval_remap`

```lean
BoolCircuit.DAGGate.eval_remap : ∀ (g : BoolCircuit.DAGGate) (σ : ℕ → ℕ) {vals vals' : List Bool},
  (∀ a ∈ g.args, vals.getD (σ a) false = vals'.getD a false) → (BoolCircuit.DAGGate.remap σ g).eval vals = g.eval vals'
```

## `BoolCircuit.DAGGate.kind`

```lean
BoolCircuit.DAGGate.kind : BoolCircuit.DAGGate → BoolCircuit.GateKind
```

## `BoolCircuit.DAGGate.mk`

```lean
BoolCircuit.DAGGate.mk : BoolCircuit.GateKind → List ℕ → BoolCircuit.DAGGate
```

## `BoolCircuit.DAGGate.mk._flat_ctor`

```lean
BoolCircuit.DAGGate.mk._flat_ctor : BoolCircuit.GateKind → List ℕ → BoolCircuit.DAGGate
```

## `BoolCircuit.DAGGate.mk.inj`

```lean
BoolCircuit.DAGGate.mk.inj : ∀ {kind : BoolCircuit.GateKind} {args : List ℕ} {kind_1 : BoolCircuit.GateKind}
  {args_1 : List ℕ}, { kind := kind, args := args } = { kind := kind_1, args := args_1 } → kind = kind_1 ∧ args = args_1
```

## `BoolCircuit.DAGGate.mk.injEq`

```lean
BoolCircuit.DAGGate.mk.injEq : ∀ (kind : BoolCircuit.GateKind) (args : List ℕ) (kind_1 : BoolCircuit.GateKind)
  (args_1 : List ℕ),
  ({ kind := kind, args := args } = { kind := kind_1, args := args_1 }) = (kind = kind_1 ∧ args = args_1)
```

## `BoolCircuit.DAGGate.mk.noConfusion`

```lean
BoolCircuit.DAGGate.mk.noConfusion : (P : Sort u) →
  (kind : BoolCircuit.GateKind) →
    (args : List ℕ) →
      (kind' : BoolCircuit.GateKind) →
        (args' : List ℕ) →
          { kind := kind, args := args } = { kind := kind', args := args' } → (kind = kind' → args = args' → P) → P
```

## `BoolCircuit.DAGGate.mk.sizeOf_spec`

```lean
BoolCircuit.DAGGate.mk.sizeOf_spec : ∀ (kind : BoolCircuit.GateKind) (args : List ℕ),
  sizeOf { kind := kind, args := args } = 1 + sizeOf kind + sizeOf args
```

## `BoolCircuit.DAGGate.noConfusion`

```lean
BoolCircuit.DAGGate.noConfusion : {P : Sort u} →
  {x1 x2 : BoolCircuit.DAGGate} → x1 = x2 → BoolCircuit.DAGGate.noConfusionType P x1 x2
```

## `BoolCircuit.DAGGate.noConfusionType`

```lean
BoolCircuit.DAGGate.noConfusionType : Sort u → BoolCircuit.DAGGate → BoolCircuit.DAGGate → Sort u
```

## `BoolCircuit.DAGGate.rec`

```lean
BoolCircuit.DAGGate.rec : {motive : BoolCircuit.DAGGate → Sort u} →
  ((kind : BoolCircuit.GateKind) → (args : List ℕ) → motive { kind := kind, args := args }) →
    (t : BoolCircuit.DAGGate) → motive t
```

## `BoolCircuit.DAGGate.recOn`

```lean
BoolCircuit.DAGGate.recOn : {motive : BoolCircuit.DAGGate → Sort u} →
  (t : BoolCircuit.DAGGate) →
    ((kind : BoolCircuit.GateKind) → (args : List ℕ) → motive { kind := kind, args := args }) → motive t
```

## `BoolCircuit.DAGGate.remap`

```lean
BoolCircuit.DAGGate.remap : (ℕ → ℕ) → BoolCircuit.DAGGate → BoolCircuit.DAGGate
```

## `BoolCircuit.DAGGate.remap.eq_1`

```lean
BoolCircuit.DAGGate.remap.eq_1 : ∀ (σ : ℕ → ℕ) (g : BoolCircuit.DAGGate),
  BoolCircuit.DAGGate.remap σ g = { kind := g.kind, args := List.map σ g.args }
```

## `BoolCircuit.DAGGate.remap_id`

```lean
BoolCircuit.DAGGate.remap_id : ∀ (g : BoolCircuit.DAGGate), BoolCircuit.DAGGate.remap id g = g
```

## `BoolCircuit.GateKind`

```lean
BoolCircuit.GateKind : Type
```

## `BoolCircuit.GateKind._sizeOf_1`

```lean
BoolCircuit.GateKind._sizeOf_1 : BoolCircuit.GateKind → ℕ
```

## `BoolCircuit.GateKind._sizeOf_inst`

```lean
BoolCircuit.GateKind._sizeOf_inst : SizeOf BoolCircuit.GateKind
```

## `BoolCircuit.GateKind.and`

```lean
BoolCircuit.GateKind.and : BoolCircuit.GateKind
```

## `BoolCircuit.GateKind.and.elim`

```lean
BoolCircuit.GateKind.and.elim : {motive : BoolCircuit.GateKind → Sort u} →
  (t : BoolCircuit.GateKind) → t.ctorIdx = 0 → motive BoolCircuit.GateKind.and → motive t
```

## `BoolCircuit.GateKind.and.sizeOf_spec`

```lean
BoolCircuit.GateKind.and.sizeOf_spec : sizeOf BoolCircuit.GateKind.and = 1
```

## `BoolCircuit.GateKind.casesOn`

```lean
BoolCircuit.GateKind.casesOn : {motive : BoolCircuit.GateKind → Sort u} →
  (t : BoolCircuit.GateKind) →
    motive BoolCircuit.GateKind.and → motive BoolCircuit.GateKind.or → motive BoolCircuit.GateKind.not → motive t
```

## `BoolCircuit.GateKind.ctorElim`

```lean
BoolCircuit.GateKind.ctorElim : {motive : BoolCircuit.GateKind → Sort u} →
  (ctorIdx : ℕ) →
    (t : BoolCircuit.GateKind) → ctorIdx = t.ctorIdx → BoolCircuit.GateKind.ctorElimType ctorIdx → motive t
```

## `BoolCircuit.GateKind.ctorElimType`

```lean
BoolCircuit.GateKind.ctorElimType : {motive : BoolCircuit.GateKind → Sort u} → ℕ → Sort (max 1 u)
```

## `BoolCircuit.GateKind.ctorIdx`

```lean
BoolCircuit.GateKind.ctorIdx : BoolCircuit.GateKind → ℕ
```

## `BoolCircuit.GateKind.encode`

```lean
BoolCircuit.GateKind.encode : BoolCircuit.GateKind → List Bool
```

## `BoolCircuit.GateKind.encode.eq_1`

```lean
BoolCircuit.GateKind.encode.eq_1 : BoolCircuit.GateKind.and.encode = [false, false]
```

## `BoolCircuit.GateKind.encode.eq_2`

```lean
BoolCircuit.GateKind.encode.eq_2 : BoolCircuit.GateKind.or.encode = [false, true]
```

## `BoolCircuit.GateKind.encode.eq_3`

```lean
BoolCircuit.GateKind.encode.eq_3 : BoolCircuit.GateKind.not.encode = [true, false]
```

## `BoolCircuit.GateKind.encode.match_1`

```lean
BoolCircuit.GateKind.encode.match_1 : (motive : BoolCircuit.GateKind → Sort u_1) →
  (x : BoolCircuit.GateKind) →
    (Unit → motive BoolCircuit.GateKind.and) →
      (Unit → motive BoolCircuit.GateKind.or) → (Unit → motive BoolCircuit.GateKind.not) → motive x
```

## `BoolCircuit.GateKind.encode_and`

```lean
BoolCircuit.GateKind.encode_and : BoolCircuit.GateKind.and.encode = [false, false]
```

## `BoolCircuit.GateKind.encode_not`

```lean
BoolCircuit.GateKind.encode_not : BoolCircuit.GateKind.not.encode = [true, false]
```

## `BoolCircuit.GateKind.encode_or`

```lean
BoolCircuit.GateKind.encode_or : BoolCircuit.GateKind.or.encode = [false, true]
```

## `BoolCircuit.GateKind.enumList`

```lean
BoolCircuit.GateKind.enumList : List BoolCircuit.GateKind
```

## `BoolCircuit.GateKind.enumList_getElem?_ctorIdx_eq`

```lean
BoolCircuit.GateKind.enumList_getElem?_ctorIdx_eq : ∀ (x : BoolCircuit.GateKind),
  BoolCircuit.GateKind.enumList[x.ctorIdx]? = some x
```

## `BoolCircuit.GateKind.enumList_nodup`

```lean
BoolCircuit.GateKind.enumList_nodup : BoolCircuit.GateKind.enumList.Nodup
```

## `BoolCircuit.GateKind.noConfusion`

```lean
BoolCircuit.GateKind.noConfusion : {P : Sort v✝} →
  {x y : BoolCircuit.GateKind} → x = y → BoolCircuit.GateKind.noConfusionType P x y
```

## `BoolCircuit.GateKind.noConfusionType`

```lean
BoolCircuit.GateKind.noConfusionType : Sort v✝ → BoolCircuit.GateKind → BoolCircuit.GateKind → Sort v✝
```

## `BoolCircuit.GateKind.not`

```lean
BoolCircuit.GateKind.not : BoolCircuit.GateKind
```

## `BoolCircuit.GateKind.not.elim`

```lean
BoolCircuit.GateKind.not.elim : {motive : BoolCircuit.GateKind → Sort u} →
  (t : BoolCircuit.GateKind) → t.ctorIdx = 2 → motive BoolCircuit.GateKind.not → motive t
```

## `BoolCircuit.GateKind.not.sizeOf_spec`

```lean
BoolCircuit.GateKind.not.sizeOf_spec : sizeOf BoolCircuit.GateKind.not = 1
```

## `BoolCircuit.GateKind.ofNat`

```lean
BoolCircuit.GateKind.ofNat : ℕ → BoolCircuit.GateKind
```

## `BoolCircuit.GateKind.ofNat_ctorIdx`

```lean
BoolCircuit.GateKind.ofNat_ctorIdx : ∀ (x : BoolCircuit.GateKind), BoolCircuit.GateKind.ofNat x.ctorIdx = x
```

## `BoolCircuit.GateKind.or`

```lean
BoolCircuit.GateKind.or : BoolCircuit.GateKind
```

## `BoolCircuit.GateKind.or.elim`

```lean
BoolCircuit.GateKind.or.elim : {motive : BoolCircuit.GateKind → Sort u} →
  (t : BoolCircuit.GateKind) → t.ctorIdx = 1 → motive BoolCircuit.GateKind.or → motive t
```

## `BoolCircuit.GateKind.or.sizeOf_spec`

```lean
BoolCircuit.GateKind.or.sizeOf_spec : sizeOf BoolCircuit.GateKind.or = 1
```

## `BoolCircuit.GateKind.rec`

```lean
BoolCircuit.GateKind.rec : {motive : BoolCircuit.GateKind → Sort u} →
  motive BoolCircuit.GateKind.and →
    motive BoolCircuit.GateKind.or → motive BoolCircuit.GateKind.not → (t : BoolCircuit.GateKind) → motive t
```

## `BoolCircuit.GateKind.recOn`

```lean
BoolCircuit.GateKind.recOn : {motive : BoolCircuit.GateKind → Sort u} →
  (t : BoolCircuit.GateKind) →
    motive BoolCircuit.GateKind.and → motive BoolCircuit.GateKind.or → motive BoolCircuit.GateKind.not → motive t
```

## `BoolCircuit.GateKind.toCtorIdx`

```lean
BoolCircuit.GateKind.toCtorIdx : BoolCircuit.GateKind → ℕ
```

## `BoolCircuit.GatesAcyclic`

```lean
BoolCircuit.GatesAcyclic : ℕ → List BoolCircuit.DAGGate → Prop
```

## `BoolCircuit.GatesAcyclic.append`

```lean
BoolCircuit.GatesAcyclic.append : ∀ {n : ℕ} {gs hs : List BoolCircuit.DAGGate},
  BoolCircuit.GatesAcyclic n gs → BoolCircuit.GatesAcyclic (n + gs.length) hs → BoolCircuit.GatesAcyclic n (gs ++ hs)
```

## `BoolCircuit.GatesAcyclic.append._proof_1_1`

```lean
BoolCircuit.GatesAcyclic.append._proof_1_1 : ∀ {gs : List BoolCircuit.DAGGate} {hs : List BoolCircuit.DAGGate}
  (i : ℕ), ¬i < gs.length → ¬gs.length ≤ i → False
```

## `BoolCircuit.GatesAcyclic.append._proof_1_2`

```lean
BoolCircuit.GatesAcyclic.append._proof_1_2 : ∀ {gs hs : List BoolCircuit.DAGGate} (i : ℕ),
  ¬i < gs.length → i < gs.length + hs.length → ¬i - gs.length < hs.length → False
```

## `BoolCircuit.GatesAcyclic.append._proof_1_3`

```lean
BoolCircuit.GatesAcyclic.append._proof_1_3 : ∀ {n : ℕ} {gs : List BoolCircuit.DAGGate}
  {hs : List BoolCircuit.DAGGate} (i a : ℕ), ¬i < gs.length → a < n + gs.length + (i - gs.length) → ¬a < n + i → False
```

## `BoolCircuit.GatesAcyclic.nil`

```lean
BoolCircuit.GatesAcyclic.nil : ∀ {n : ℕ}, BoolCircuit.GatesAcyclic n []
```

## `BoolCircuit.GatesAcyclic.snoc`

```lean
BoolCircuit.GatesAcyclic.snoc : ∀ {n : ℕ} {gs : List BoolCircuit.DAGGate},
  BoolCircuit.GatesAcyclic n gs →
    ∀ {g : BoolCircuit.DAGGate}, (∀ a ∈ g.args, a < n + gs.length) → BoolCircuit.GatesAcyclic n (gs ++ [g])
```

## `BoolCircuit.all_congr_mem`

```lean
BoolCircuit.all_congr_mem : ∀ {α : Type} {l : List α} {p q : α → Bool}, (∀ a ∈ l, p a = q a) → l.all p = l.all q
```

## `BoolCircuit.any_congr_mem`

```lean
BoolCircuit.any_congr_mem : ∀ {α : Type} {l : List α} {p q : α → Bool}, (∀ a ∈ l, p a = q a) → l.any p = l.any q
```

## `BoolCircuit.constCircuit`

```lean
BoolCircuit.constCircuit : (n : ℕ) → Bool → BoolCircuit.DAGCircuit n
```

## `BoolCircuit.constCircuit._proof_1`

```lean
BoolCircuit.constCircuit._proof_1 : ∀ (n : ℕ) (b : Bool) (i : ℕ) (hi : i < [BoolCircuit.constGate b].length),
  ∀ a ∈ [BoolCircuit.constGate b][i].args, a < n + i
```

## `BoolCircuit.constCircuit._proof_2`

```lean
BoolCircuit.constCircuit._proof_2 : ∀ (n : ℕ), n < n + (0 + 1)
```

## `BoolCircuit.constCircuit.eq_1`

```lean
BoolCircuit.constCircuit.eq_1 : ∀ (n : ℕ) (b : Bool),
  BoolCircuit.constCircuit n b = { gates := [BoolCircuit.constGate b], output := n, args_lt := ⋯, output_lt := ⋯ }
```

## `BoolCircuit.constCircuit_eval`

```lean
BoolCircuit.constCircuit_eval : ∀ {n : ℕ} (b : Bool) (x : Fin n → Bool),
  (BoolCircuit.constCircuit n b).eval x = b
```

## `BoolCircuit.constCircuit_isFaninTwo`

```lean
BoolCircuit.constCircuit_isFaninTwo : ∀ (n : ℕ) (b : Bool), (BoolCircuit.constCircuit n b).IsFaninTwo
```

## `BoolCircuit.constCircuit_isFaninTwo._simp_1_2`

```lean
BoolCircuit.constCircuit_isFaninTwo._simp_1_2 : ∀ {α : Type u_1} {a b : α}, (a ∈ [b]) = (a = b)
```

## `BoolCircuit.constCircuit_size`

```lean
BoolCircuit.constCircuit_size : ∀ (n : ℕ) (b : Bool), (BoolCircuit.constCircuit n b).size = n + 1
```

## `BoolCircuit.constGate`

```lean
BoolCircuit.constGate : Bool → BoolCircuit.DAGGate
```

## `BoolCircuit.constGate.eq_1`

```lean
BoolCircuit.constGate.eq_1 : ∀ (b : Bool),
  BoolCircuit.constGate b =
    { kind := if b = true then BoolCircuit.GateKind.and else BoolCircuit.GateKind.or, args := [] }
```

## `BoolCircuit.constGate_args`

```lean
BoolCircuit.constGate_args : ∀ (b : Bool), (BoolCircuit.constGate b).args = []
```

## `BoolCircuit.constGate_depth`

```lean
BoolCircuit.constGate_depth : ∀ (b : Bool) (ds : List ℕ), (BoolCircuit.constGate b).depth ds = 1
```

## `BoolCircuit.constGate_eval`

```lean
BoolCircuit.constGate_eval : ∀ (b : Bool) (vals : List Bool), (BoolCircuit.constGate b).eval vals = b
```

## `BoolCircuit.constGate_false`

```lean
BoolCircuit.constGate_false : BoolCircuit.constGate false = { kind := BoolCircuit.GateKind.or, args := [] }
```

## `BoolCircuit.constGate_faninTwo`

```lean
BoolCircuit.constGate_faninTwo : ∀ (b : Bool), (BoolCircuit.constGate b).FaninTwo
```

## `BoolCircuit.constGate_faninTwo._simp_1`

```lean
BoolCircuit.constGate_faninTwo._simp_1 : ∀ (b : Bool), (BoolCircuit.constGate b).FaninTwo = True
```

## `BoolCircuit.constGate_kind_ne_not`

```lean
BoolCircuit.constGate_kind_ne_not : ∀ (b : Bool), (BoolCircuit.constGate b).kind ≠ BoolCircuit.GateKind.not
```

## `BoolCircuit.constGate_true`

```lean
BoolCircuit.constGate_true : BoolCircuit.constGate true = { kind := BoolCircuit.GateKind.and, args := [] }
```

## `BoolCircuit.encodeList`

```lean
BoolCircuit.encodeList : {α : Type} → (α → List Bool) → List α → List Bool
```

## `BoolCircuit.encodeList._sunfold`

```lean
BoolCircuit.encodeList._sunfold : {α : Type} → (α → List Bool) → List α → List Bool
```

## `BoolCircuit.encodeList._unsafe_rec`

```lean
BoolCircuit.encodeList._unsafe_rec : {α : Type} → (α → List Bool) → List α → List Bool
```

## `BoolCircuit.encodeList.eq_1`

```lean
BoolCircuit.encodeList.eq_1 : ∀ {α : Type} (f : α → List Bool), BoolCircuit.encodeList f [] = [false]
```

## `BoolCircuit.encodeList.eq_2`

```lean
BoolCircuit.encodeList.eq_2 : ∀ {α : Type} (f : α → List Bool) (a : α) (as : List α),
  BoolCircuit.encodeList f (a :: as) = true :: (f a ++ BoolCircuit.encodeList f as)
```

## `BoolCircuit.encodeList.eq_def`

```lean
BoolCircuit.encodeList.eq_def : ∀ {α : Type} (f : α → List Bool) (x : List α),
  BoolCircuit.encodeList f x =
    match x with
    | [] => [false]
    | a :: as => true :: (f a ++ BoolCircuit.encodeList f as)
```

## `BoolCircuit.encodeList.match_1`

```lean
BoolCircuit.encodeList.match_1 : {α : Type} →
  (motive : List α → Sort u_1) →
    (x : List α) → (Unit → motive []) → ((a : α) → (as : List α) → motive (a :: as)) → motive x
```

## `BoolCircuit.encodeList_cons`

```lean
BoolCircuit.encodeList_cons : ∀ {α : Type} (f : α → List Bool) (a : α) (as : List α),
  BoolCircuit.encodeList f (a :: as) = true :: (f a ++ BoolCircuit.encodeList f as)
```

## `BoolCircuit.encodeList_nil`

```lean
BoolCircuit.encodeList_nil : ∀ {α : Type} (f : α → List Bool), BoolCircuit.encodeList f [] = [false]
```

## `BoolCircuit.gatesAcyclic_append`

```lean
BoolCircuit.gatesAcyclic_append : ∀ {n : ℕ} {gs hs : List BoolCircuit.DAGGate},
  BoolCircuit.GatesAcyclic n (gs ++ hs) ↔ BoolCircuit.GatesAcyclic n gs ∧ BoolCircuit.GatesAcyclic (n + gs.length) hs
```

## `BoolCircuit.gatesAcyclic_append._proof_1_2`

```lean
BoolCircuit.gatesAcyclic_append._proof_1_2 : ∀ (gs : List BoolCircuit.DAGGate) {n : ℕ},
  ¬n + 1 + gs.length = n + (gs.length + 1) → False
```

## `BoolCircuit.gatesAcyclic_append._simp_1_1`

```lean
BoolCircuit.gatesAcyclic_append._simp_1_1 : ∀ {a b c : Prop}, ((a ∧ b) ∧ c) = (a ∧ b ∧ c)
```

## `BoolCircuit.gatesAcyclic_cons`

```lean
BoolCircuit.gatesAcyclic_cons : ∀ {n : ℕ} {g : BoolCircuit.DAGGate} {gs : List BoolCircuit.DAGGate},
  BoolCircuit.GatesAcyclic n (g :: gs) ↔ (∀ a ∈ g.args, a < n) ∧ BoolCircuit.GatesAcyclic (n + 1) gs
```

## `BoolCircuit.gatesAcyclic_cons._proof_1_1`

```lean
BoolCircuit.gatesAcyclic_cons._proof_1_1 : ∀ {n : ℕ} {gs : List BoolCircuit.DAGGate} (i a : ℕ),
  a < n + (i + 1) → ¬a < n + 1 + i → False
```

## `BoolCircuit.gatesAcyclic_cons._proof_1_2`

```lean
BoolCircuit.gatesAcyclic_cons._proof_1_2 : ∀ {n : ℕ} {g : BoolCircuit.DAGGate} {gs : List BoolCircuit.DAGGate}
  (a i : ℕ), a < n + 1 + i → ¬a < n + (i + 1) → False
```

## `BoolCircuit.gatesAcyclic_cons._simp_1`

```lean
BoolCircuit.gatesAcyclic_cons._simp_1 : ∀ {n : ℕ} {g : BoolCircuit.DAGGate} {gs : List BoolCircuit.DAGGate},
  BoolCircuit.GatesAcyclic n (g :: gs) = ((∀ a ∈ g.args, a < n) ∧ BoolCircuit.GatesAcyclic (n + 1) gs)
```

## `BoolCircuit.gatesAcyclic_nil`

```lean
BoolCircuit.gatesAcyclic_nil : ∀ {n : ℕ}, BoolCircuit.GatesAcyclic n [] ↔ True
```

## `BoolCircuit.gatesAcyclic_nil._simp_1`

```lean
BoolCircuit.gatesAcyclic_nil._simp_1 : ∀ {n : ℕ}, BoolCircuit.GatesAcyclic n [] = True
```

## `BoolCircuit.instDecidableEqDAGGate`

```lean
BoolCircuit.instDecidableEqDAGGate : DecidableEq BoolCircuit.DAGGate
```

## `BoolCircuit.instDecidableEqDAGGate.decEq`

```lean
BoolCircuit.instDecidableEqDAGGate.decEq : (x x_1 : BoolCircuit.DAGGate) → Decidable (x = x_1)
```

## `BoolCircuit.instDecidableEqDAGGate.decEq._proof_1`

```lean
BoolCircuit.instDecidableEqDAGGate.decEq._proof_1 : ∀ (a : BoolCircuit.GateKind) (a_1 : List ℕ),
  { kind := a, args := a_1 } = { kind := a, args := a_1 }
```

## `BoolCircuit.instDecidableEqDAGGate.decEq._proof_2`

```lean
BoolCircuit.instDecidableEqDAGGate.decEq._proof_2 : ∀ (a : BoolCircuit.GateKind) (a_1 b : List ℕ),
  ¬a_1 = b → { kind := a, args := a_1 } = { kind := a, args := b } → False
```

## `BoolCircuit.instDecidableEqDAGGate.decEq._proof_3`

```lean
BoolCircuit.instDecidableEqDAGGate.decEq._proof_3 : ∀ (a : BoolCircuit.GateKind) (a_1 : List ℕ)
  (b : BoolCircuit.GateKind) (b_1 : List ℕ), ¬a = b → { kind := a, args := a_1 } = { kind := b, args := b_1 } → False
```

## `BoolCircuit.instDecidableEqDAGGate.decEq.match_1`

```lean
BoolCircuit.instDecidableEqDAGGate.decEq.match_1 : (motive :
    BoolCircuit.DAGGate → BoolCircuit.DAGGate → Sort u_1) →
  (x x_1 : BoolCircuit.DAGGate) →
    ((a : BoolCircuit.GateKind) →
        (a_1 : List ℕ) →
          (b : BoolCircuit.GateKind) → (b_1 : List ℕ) → motive { kind := a, args := a_1 } { kind := b, args := b_1 }) →
      motive x x_1
```

## `BoolCircuit.instDecidableEqGateKind`

```lean
BoolCircuit.instDecidableEqGateKind : DecidableEq BoolCircuit.GateKind
```

## `BoolCircuit.instDecidableEqGateKind._proof_1`

```lean
BoolCircuit.instDecidableEqGateKind._proof_1 : ∀ (x y : BoolCircuit.GateKind), x.ctorIdx = y.ctorIdx → x = y
```

## `BoolCircuit.instDecidableEqGateKind._proof_2`

```lean
BoolCircuit.instDecidableEqGateKind._proof_2 : ∀ (x y : BoolCircuit.GateKind),
  ¬x.ctorIdx = y.ctorIdx → x = y → False
```

## `BoolCircuit.instFintypeGateKind`

```lean
BoolCircuit.instFintypeGateKind : Fintype BoolCircuit.GateKind
```

## `BoolCircuit.instFintypeGateKind._proof_1`

```lean
BoolCircuit.instFintypeGateKind._proof_1 : ∀ (x : BoolCircuit.GateKind),
  x ∈ { val := ↑BoolCircuit.GateKind.enumList, nodup := BoolCircuit.GateKind.enumList_nodup }
```

## `BoolCircuit.instReprDAGGate`

```lean
BoolCircuit.instReprDAGGate : Repr BoolCircuit.DAGGate
```

## `BoolCircuit.instReprDAGGate.repr`

```lean
BoolCircuit.instReprDAGGate.repr : BoolCircuit.DAGGate → ℕ → Format
```

## `BoolCircuit.instReprGateKind`

```lean
BoolCircuit.instReprGateKind : Repr BoolCircuit.GateKind
```

## `BoolCircuit.instReprGateKind.repr`

```lean
BoolCircuit.instReprGateKind.repr : BoolCircuit.GateKind → ℕ → Format
```

## `BoolCircuit.instReprGateKind.repr.match_1`

```lean
BoolCircuit.instReprGateKind.repr.match_1 : (motive : BoolCircuit.GateKind → Sort u_1) →
  (x : BoolCircuit.GateKind) →
    (Unit → motive BoolCircuit.GateKind.and) →
      (Unit → motive BoolCircuit.GateKind.or) → (Unit → motive BoolCircuit.GateKind.not) → motive x
```

## `BoolCircuit.length_encodeList_ge`

```lean
BoolCircuit.length_encodeList_ge : ∀ {α : Type} (f : α → List Bool) (as : List α),
  as.length + 1 ≤ (BoolCircuit.encodeList f as).length
```

## `BoolCircuit.length_encodeList_ge._proof_1_4`

```lean
BoolCircuit.length_encodeList_ge._proof_1_4 : ∀ {α : Type} (f : α → List Bool) (a : α) (as : List α),
  as.length + 1 ≤ (BoolCircuit.encodeList f as).length →
    ¬as.length + 1 + 1 ≤ (f a).length + (BoolCircuit.encodeList f as).length + 1 → False
```

## `BoolCircuit.length_runWith`

```lean
BoolCircuit.length_runWith : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (gs : List BoolCircuit.DAGGate)
  (init : List β), (BoolCircuit.runWith f gs init).length = init.length + gs.length
```

## `BoolCircuit.length_runWith._proof_1_1`

```lean
BoolCircuit.length_runWith._proof_1_1 : ∀ {β : Type} (gs : List BoolCircuit.DAGGate) (init : List β),
  ¬init.length + 1 + gs.length = init.length + (gs.length + 1) → False
```

## `BoolCircuit.runWith`

```lean
BoolCircuit.runWith : {β : Type} →
  (BoolCircuit.DAGGate → List β → β) → List BoolCircuit.DAGGate → List β → List β
```

## `BoolCircuit.runWith.eq_1`

```lean
BoolCircuit.runWith.eq_1 : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (gs : List BoolCircuit.DAGGate)
  (init : List β), BoolCircuit.runWith f gs init = List.foldl (fun vs g => vs ++ [f g vs]) init gs
```

## `BoolCircuit.runWith_append`

```lean
BoolCircuit.runWith_append : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β)
  (gs hs : List BoolCircuit.DAGGate) (init : List β),
  BoolCircuit.runWith f (gs ++ hs) init = BoolCircuit.runWith f hs (BoolCircuit.runWith f gs init)
```

## `BoolCircuit.runWith_cons`

```lean
BoolCircuit.runWith_cons : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (g : BoolCircuit.DAGGate)
  (gs : List BoolCircuit.DAGGate) (init : List β),
  BoolCircuit.runWith f (g :: gs) init = BoolCircuit.runWith f gs (init ++ [f g init])
```

## `BoolCircuit.runWith_eq_append`

```lean
BoolCircuit.runWith_eq_append : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β)
  (gs : List BoolCircuit.DAGGate) (init : List β), ∃ ext, BoolCircuit.runWith f gs init = init ++ ext
```

## `BoolCircuit.runWith_getD_gate`

```lean
BoolCircuit.runWith_getD_gate : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β)
  (gs : List BoolCircuit.DAGGate) (init : List β) {i : ℕ} (hi : i < gs.length) (d : β),
  (BoolCircuit.runWith f gs init).getD (init.length + i) d = f gs[i] (BoolCircuit.runWith f (List.take i gs) init)
```

## `BoolCircuit.runWith_getD_last`

```lean
BoolCircuit.runWith_getD_last : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β)
  (gs : List BoolCircuit.DAGGate) (g : BoolCircuit.DAGGate) (init : List β) (d : β),
  (BoolCircuit.runWith f (gs ++ [g]) init).getD (init.length + gs.length) d = f g (BoolCircuit.runWith f gs init)
```

## `BoolCircuit.runWith_getD_last._proof_1_1`

```lean
BoolCircuit.runWith_getD_last._proof_1_1 : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β)
  (gs : List BoolCircuit.DAGGate) (init : List β),
  (BoolCircuit.runWith f gs init).length = init.length + gs.length →
    ¬(BoolCircuit.runWith f gs init).length ≤ init.length + gs.length → False
```

## `BoolCircuit.runWith_getD_of_lt`

```lean
BoolCircuit.runWith_getD_of_lt : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β)
  (gs : List BoolCircuit.DAGGate) (init : List β) {v : ℕ},
  v < init.length → ∀ (d : β), (BoolCircuit.runWith f gs init).getD v d = init.getD v d
```

## `BoolCircuit.runWith_getD_take`

```lean
BoolCircuit.runWith_getD_take : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β)
  (gs : List BoolCircuit.DAGGate) (init : List β) {i a : ℕ},
  i ≤ gs.length →
    a < init.length + i →
      ∀ (d : β), (BoolCircuit.runWith f (List.take i gs) init).getD a d = (BoolCircuit.runWith f gs init).getD a d
```

## `BoolCircuit.runWith_nil`

```lean
BoolCircuit.runWith_nil : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (init : List β),
  BoolCircuit.runWith f [] init = init
```

## `BoolCircuit.runWith_remap_rel`

```lean
BoolCircuit.runWith_remap_rel : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (R : β → β → Prop) (d : β)
  (σ : ℕ → ℕ),
  (∀ (g : BoolCircuit.DAGGate) (vs vs' : List β),
      (∀ a ∈ g.args, R (vs.getD (σ a) d) (vs'.getD a d)) → R (f (BoolCircuit.DAGGate.remap σ g) vs) (f g vs')) →
    ∀ {L L' : ℕ} (init init' : List β),
      init.length = L →
        init'.length = L' →
          (∀ v < L, σ v < L') →
            (∀ (i : ℕ), σ (L + i) = L' + i) →
              (∀ v < L, R (init'.getD (σ v) d) (init.getD v d)) →
                ∀ (gs : List BoolCircuit.DAGGate),
                  (∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ gs[i].args, a < L + i) →
                    ∀ v < L + gs.length,
                      R ((BoolCircuit.runWith f (List.map (BoolCircuit.DAGGate.remap σ) gs) init').getD (σ v) d)
                        ((BoolCircuit.runWith f gs init).getD v d)
```

## `BoolCircuit.runWith_remap_rel._proof_1_1`

```lean
BoolCircuit.runWith_remap_rel._proof_1_1 : ∀ {β : Type} {L L' : ℕ} (init init' : List β)
  (old : List BoolCircuit.DAGGate), ∀ i < old.length, ¬i < old.length + 1 → False
```

## `BoolCircuit.runWith_remap_rel._proof_1_2`

```lean
BoolCircuit.runWith_remap_rel._proof_1_2 : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (σ : ℕ → ℕ)
  {L : ℕ} {L' : ℕ} (init init' : List β) (old : List BoolCircuit.DAGGate),
  (BoolCircuit.runWith f (List.map (BoolCircuit.DAGGate.remap σ) old) init').length = L' + old.length →
    ∀ (v : ℕ), σ v < L' → ¬σ v < L' + old.length → False
```

## `BoolCircuit.runWith_remap_rel._proof_1_3`

```lean
BoolCircuit.runWith_remap_rel._proof_1_3 : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (σ : ℕ → ℕ)
  {L L' : ℕ} (init init' : List β) (old : List BoolCircuit.DAGGate) (i : ℕ),
  L + i < L + old.length → ¬L' + i < L' + old.length → False
```

## `BoolCircuit.runWith_remap_rel._proof_1_4`

```lean
BoolCircuit.runWith_remap_rel._proof_1_4 : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (σ : ℕ → ℕ)
  {L : ℕ} {L' : ℕ} (init init' : List β) (old : List BoolCircuit.DAGGate),
  (BoolCircuit.runWith f old init).length = L + old.length → ∀ v < L + (old.length + 1), ¬v < L + old.length + 1 → False
```

## `BoolCircuit.runWith_remap_rel._proof_1_5`

```lean
BoolCircuit.runWith_remap_rel._proof_1_5 : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (σ : ℕ → ℕ)
  {L : ℕ} {L' : ℕ} (init init' : List β) (old : List BoolCircuit.DAGGate),
  (BoolCircuit.runWith f (List.map (BoolCircuit.DAGGate.remap σ) old) init').length = L' + old.length →
    ¬(BoolCircuit.runWith f (List.map (BoolCircuit.DAGGate.remap σ) old) init').length ≤ L' + old.length → False
```

## `BoolCircuit.runWith_remap_rel._proof_1_6`

```lean
BoolCircuit.runWith_remap_rel._proof_1_6 : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (σ : ℕ → ℕ)
  {L : ℕ} {L' : ℕ} (init init' : List β) (old : List BoolCircuit.DAGGate),
  (BoolCircuit.runWith f old init).length = L + old.length →
    ¬(BoolCircuit.runWith f old init).length ≤ L + old.length → False
```

## `BoolCircuit.runWith_singleton`

```lean
BoolCircuit.runWith_singleton : ∀ {β : Type} (f : BoolCircuit.DAGGate → List β → β) (g : BoolCircuit.DAGGate)
  (init : List β), BoolCircuit.runWith f [g] init = init ++ [f g init]
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit : Type
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit._sizeOf_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit._sizeOf_1 : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit._sizeOf_inst`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit._sizeOf_inst : SizeOf
  TCSlib.Cryptography.SecureComputation.YaoCircuit
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.casesOn`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.casesOn : {motive :
    TCSlib.Cryptography.SecureComputation.YaoCircuit → Sort u} →
  (t : TCSlib.Cryptography.SecureComputation.YaoCircuit) →
    ((inA inB outLen sizeBound : Complexity.PolyExpr) →
        (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n)) →
          (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
            (outs_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size) →
              (outs_sink : ∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args) →
                (fanin : ∀ (n : ℕ), (circ n).IsFaninTwo) →
                  (size_le : ∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n) →
                    (uniform :
                        ∃ E,
                          Complexity.PolyTimeComputable E ∧
                            ∀ (n : ℕ),
                              E (List.replicate n true) =
                                TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n)) →
                      motive
                        { inA := inA, inB := inB, outLen := outLen, sizeBound := sizeBound, circ := circ, outs := outs,
                          outs_lt := outs_lt, outs_sink := outs_sink, fanin := fanin, size_le := size_le,
                          uniform := uniform }) →
      motive t
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.circ`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.circ : (self :
    TCSlib.Cryptography.SecureComputation.YaoCircuit) →
  (n : ℕ) → BoolCircuit.DAGCircuit (self.inA.eval n + self.inB.eval n)
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.ctorIdx`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.ctorIdx : TCSlib.Cryptography.SecureComputation.YaoCircuit → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.fanin`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.fanin : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ), (self.circ n).IsFaninTwo
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.inA`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.inA : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.inB`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.inB : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.mk`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.mk : (inA inB outLen sizeBound : Complexity.PolyExpr) →
  (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n)) →
    (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
      (∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size) →
        (∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args) →
          (∀ (n : ℕ), (circ n).IsFaninTwo) →
            (∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n) →
              (∃ E,
                  Complexity.PolyTimeComputable E ∧
                    ∀ (n : ℕ),
                      E (List.replicate n true) =
                        TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n)) →
                TCSlib.Cryptography.SecureComputation.YaoCircuit
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.mk._flat_ctor`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.mk._flat_ctor : (inA inB outLen sizeBound :
    Complexity.PolyExpr) →
  (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n)) →
    (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
      (∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size) →
        (∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args) →
          (∀ (n : ℕ), (circ n).IsFaninTwo) →
            (∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n) →
              (∃ E,
                  Complexity.PolyTimeComputable E ∧
                    ∀ (n : ℕ),
                      E (List.replicate n true) =
                        TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n)) →
                TCSlib.Cryptography.SecureComputation.YaoCircuit
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.mk.inj`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.mk.inj : ∀ {inA inB outLen sizeBound : Complexity.PolyExpr}
  {circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n)} {outs : (n : ℕ) → Fin (outLen.eval n) → ℕ}
  {outs_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size}
  {outs_sink : ∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args}
  {fanin : ∀ (n : ℕ), (circ n).IsFaninTwo} {size_le : ∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n}
  {uniform :
    ∃ E,
      Complexity.PolyTimeComputable E ∧
        ∀ (n : ℕ), E (List.replicate n true) = TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n)}
  {inA_1 inB_1 outLen_1 sizeBound_1 : Complexity.PolyExpr}
  {circ_1 : (n : ℕ) → BoolCircuit.DAGCircuit (inA_1.eval n + inB_1.eval n)}
  {outs_1 : (n : ℕ) → Fin (outLen_1.eval n) → ℕ}
  {outs_lt_1 : ∀ (n : ℕ) (j : Fin (outLen_1.eval n)), outs_1 n j < (circ_1 n).size}
  {outs_sink_1 : ∀ (n : ℕ) (j : Fin (outLen_1.eval n)), ∀ g ∈ (circ_1 n).gates, outs_1 n j ∉ g.args}
  {fanin_1 : ∀ (n : ℕ), (circ_1 n).IsFaninTwo} {size_le_1 : ∀ (n : ℕ), (circ_1 n).size ≤ sizeBound_1.eval n}
  {uniform_1 :
    ∃ E,
      Complexity.PolyTimeComputable E ∧
        ∀ (n : ℕ),
          E (List.replicate n true) = TCSlib.Cryptography.SecureComputation.encodeCircuit (circ_1 n) (outs_1 n)},
  { inA := inA, inB := inB, outLen := outLen, sizeBound := sizeBound, circ := circ, outs := outs, outs_lt := outs_lt,
        outs_sink := outs_sink, fanin := fanin, size_le := size_le, uniform := uniform } =
      { inA := inA_1, inB := inB_1, outLen := outLen_1, sizeBound := sizeBound_1, circ := circ_1, outs := outs_1,
        outs_lt := outs_lt_1, outs_sink := outs_sink_1, fanin := fanin_1, size_le := size_le_1, uniform := uniform_1 } →
    inA = inA_1 ∧ inB = inB_1 ∧ outLen = outLen_1 ∧ sizeBound = sizeBound_1 ∧ circ ≍ circ_1 ∧ outs ≍ outs_1
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.mk.injEq`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.mk.injEq : ∀ (inA inB outLen sizeBound : Complexity.PolyExpr)
  (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n)) (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (outs_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size)
  (outs_sink : ∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args)
  (fanin : ∀ (n : ℕ), (circ n).IsFaninTwo) (size_le : ∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n)
  (uniform :
    ∃ E,
      Complexity.PolyTimeComputable E ∧
        ∀ (n : ℕ), E (List.replicate n true) = TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n))
  (inA_1 inB_1 outLen_1 sizeBound_1 : Complexity.PolyExpr)
  (circ_1 : (n : ℕ) → BoolCircuit.DAGCircuit (inA_1.eval n + inB_1.eval n))
  (outs_1 : (n : ℕ) → Fin (outLen_1.eval n) → ℕ)
  (outs_lt_1 : ∀ (n : ℕ) (j : Fin (outLen_1.eval n)), outs_1 n j < (circ_1 n).size)
  (outs_sink_1 : ∀ (n : ℕ) (j : Fin (outLen_1.eval n)), ∀ g ∈ (circ_1 n).gates, outs_1 n j ∉ g.args)
  (fanin_1 : ∀ (n : ℕ), (circ_1 n).IsFaninTwo) (size_le_1 : ∀ (n : ℕ), (circ_1 n).size ≤ sizeBound_1.eval n)
  (uniform_1 :
    ∃ E,
      Complexity.PolyTimeComputable E ∧
        ∀ (n : ℕ),
          E (List.replicate n true) = TCSlib.Cryptography.SecureComputation.encodeCircuit (circ_1 n) (outs_1 n)),
  ({ inA := inA, inB := inB, outLen := outLen, sizeBound := sizeBound, circ := circ, outs := outs, outs_lt := outs_lt,
        outs_sink := outs_sink, fanin := fanin, size_le := size_le, uniform := uniform } =
      { inA := inA_1, inB := inB_1, outLen := outLen_1, sizeBound := sizeBound_1, circ := circ_1, outs := outs_1,
        outs_lt := outs_lt_1, outs_sink := outs_sink_1, fanin := fanin_1, size_le := size_le_1,
        uniform := uniform_1 }) =
    (inA = inA_1 ∧ inB = inB_1 ∧ outLen = outLen_1 ∧ sizeBound = sizeBound_1 ∧ circ ≍ circ_1 ∧ outs ≍ outs_1)
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.mk.noConfusion`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.mk.noConfusion : (P : Sort u) →
  (inA inB outLen sizeBound : Complexity.PolyExpr) →
    (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n)) →
      (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
        (outs_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size) →
          (outs_sink : ∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args) →
            (fanin : ∀ (n : ℕ), (circ n).IsFaninTwo) →
              (size_le : ∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n) →
                (uniform :
                    ∃ E,
                      Complexity.PolyTimeComputable E ∧
                        ∀ (n : ℕ),
                          E (List.replicate n true) =
                            TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n)) →
                  (inA' inB' outLen' sizeBound' : Complexity.PolyExpr) →
                    (circ' : (n : ℕ) → BoolCircuit.DAGCircuit (inA'.eval n + inB'.eval n)) →
                      (outs' : (n : ℕ) → Fin (outLen'.eval n) → ℕ) →
                        (outs_lt' : ∀ (n : ℕ) (j : Fin (outLen'.eval n)), outs' n j < (circ' n).size) →
                          (outs_sink' :
                              ∀ (n : ℕ) (j : Fin (outLen'.eval n)), ∀ g ∈ (circ' n).gates, outs' n j ∉ g.args) →
                            (fanin' : ∀ (n : ℕ), (circ' n).IsFaninTwo) →
                              (size_le' : ∀ (n : ℕ), (circ' n).size ≤ sizeBound'.eval n) →
                                (uniform' :
                                    ∃ E,
                                      Complexity.PolyTimeComputable E ∧
                                        ∀ (n : ℕ),
                                          E (List.replicate n true) =
                                            TCSlib.Cryptography.SecureComputation.encodeCircuit (circ' n) (outs' n)) →
                                  { inA := inA, inB := inB, outLen := outLen, sizeBound := sizeBound, circ := circ,
                                        outs := outs, outs_lt := outs_lt, outs_sink := outs_sink, fanin := fanin,
                                        size_le := size_le, uniform := uniform } =
                                      { inA := inA', inB := inB', outLen := outLen', sizeBound := sizeBound',
                                        circ := circ', outs := outs', outs_lt := outs_lt', outs_sink := outs_sink',
                                        fanin := fanin', size_le := size_le', uniform := uniform' } →
                                    (inA = inA' →
                                        inB = inB' →
                                          outLen = outLen' → sizeBound = sizeBound' → circ ≍ circ' → outs ≍ outs' → P) →
                                      P
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.mk.sizeOf_spec`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.mk.sizeOf_spec : ∀
  (inA inB outLen sizeBound : Complexity.PolyExpr) (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n))
  (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ) (outs_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size)
  (outs_sink : ∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args)
  (fanin : ∀ (n : ℕ), (circ n).IsFaninTwo) (size_le : ∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n)
  (uniform :
    ∃ E,
      Complexity.PolyTimeComputable E ∧
        ∀ (n : ℕ), E (List.replicate n true) = TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n)),
  sizeOf
      { inA := inA, inB := inB, outLen := outLen, sizeBound := sizeBound, circ := circ, outs := outs,
        outs_lt := outs_lt, outs_sink := outs_sink, fanin := fanin, size_le := size_le, uniform := uniform } =
    1 + sizeOf inA + sizeOf inB + sizeOf outLen + sizeOf sizeBound + sizeOf uniform
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.noConfusion`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.noConfusion : {P : Sort u} →
  {x1 x2 : TCSlib.Cryptography.SecureComputation.YaoCircuit} →
    x1 = x2 → TCSlib.Cryptography.SecureComputation.YaoCircuit.noConfusionType P x1 x2
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.noConfusionType`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.noConfusionType : Sort u →
  TCSlib.Cryptography.SecureComputation.YaoCircuit → TCSlib.Cryptography.SecureComputation.YaoCircuit → Sort u
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.outLen`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.outLen : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.output`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.output : (Y :
    TCSlib.Cryptography.SecureComputation.YaoCircuit) →
  (n : ℕ) → (Fin (Y.inA.eval n) → Bool) → (Fin (Y.inB.eval n) → Bool) → Fin (Y.outLen.eval n) → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.output_apply`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.output_apply : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
  (y : Fin (Y.inB.eval n) → Bool) (j : Fin (Y.outLen.eval n)),
  Y.output n x y j = ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.outs`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.outs : (self :
    TCSlib.Cryptography.SecureComputation.YaoCircuit) →
  (n : ℕ) → Fin (self.outLen.eval n) → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.outs_lt`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.outs_lt : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (j : Fin (self.outLen.eval n)),
  self.outs n j < (self.circ n).size
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.outs_sink`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.outs_sink : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (j : Fin (self.outLen.eval n)),
  ∀ g ∈ (self.circ n).gates, self.outs n j ∉ g.args
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.rec`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.rec : {motive :
    TCSlib.Cryptography.SecureComputation.YaoCircuit → Sort u} →
  ((inA inB outLen sizeBound : Complexity.PolyExpr) →
      (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n)) →
        (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
          (outs_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size) →
            (outs_sink : ∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args) →
              (fanin : ∀ (n : ℕ), (circ n).IsFaninTwo) →
                (size_le : ∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n) →
                  (uniform :
                      ∃ E,
                        Complexity.PolyTimeComputable E ∧
                          ∀ (n : ℕ),
                            E (List.replicate n true) =
                              TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n)) →
                    motive
                      { inA := inA, inB := inB, outLen := outLen, sizeBound := sizeBound, circ := circ, outs := outs,
                        outs_lt := outs_lt, outs_sink := outs_sink, fanin := fanin, size_le := size_le,
                        uniform := uniform }) →
    (t : TCSlib.Cryptography.SecureComputation.YaoCircuit) → motive t
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.recOn`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.recOn : {motive :
    TCSlib.Cryptography.SecureComputation.YaoCircuit → Sort u} →
  (t : TCSlib.Cryptography.SecureComputation.YaoCircuit) →
    ((inA inB outLen sizeBound : Complexity.PolyExpr) →
        (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n)) →
          (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
            (outs_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size) →
              (outs_sink : ∀ (n : ℕ) (j : Fin (outLen.eval n)), ∀ g ∈ (circ n).gates, outs n j ∉ g.args) →
                (fanin : ∀ (n : ℕ), (circ n).IsFaninTwo) →
                  (size_le : ∀ (n : ℕ), (circ n).size ≤ sizeBound.eval n) →
                    (uniform :
                        ∃ E,
                          Complexity.PolyTimeComputable E ∧
                            ∀ (n : ℕ),
                              E (List.replicate n true) =
                                TCSlib.Cryptography.SecureComputation.encodeCircuit (circ n) (outs n)) →
                      motive
                        { inA := inA, inB := inB, outLen := outLen, sizeBound := sizeBound, circ := circ, outs := outs,
                          outs_lt := outs_lt, outs_sink := outs_sink, fanin := fanin, size_le := size_le,
                          uniform := uniform }) →
      motive t
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.sizeBound`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.sizeBound : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.size_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.size_le : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ), (self.circ n).size ≤ self.sizeBound.eval n
```

## `TCSlib.Cryptography.SecureComputation.YaoCircuit.uniform`

```lean
TCSlib.Cryptography.SecureComputation.YaoCircuit.uniform : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoCircuit),
  ∃ E,
    Complexity.PolyTimeComputable E ∧
      ∀ (n : ℕ),
        E (List.replicate n true) = TCSlib.Cryptography.SecureComputation.encodeCircuit (self.circ n) (self.outs n)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.message_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.message_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ (width bound inputs inA outLen : List Bool → ℕ) (description xs coins : List Bool → List Bool),
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              (Complexity.PolyTimeComputable fun z => List.replicate (inA z) true) →
                (Complexity.PolyTimeComputable fun z => List.replicate (outLen z) true) →
                  Complexity.PolyTimeComputable description →
                    Complexity.PolyTimeComputable xs →
                      Complexity.PolyTimeComputable coins →
                        ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
                          (s :
                            (z : List Bool) →
                              TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                                ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
                          (output : (z : List Bool) → Fin (outLen z) → ℕ),
                          (∀ (z : List Bool),
                              description z =
                                Turing.pairEncode (C z).encode
                                  (Complexity.BinArith.encWords
                                    (List.ofFn fun j => BoolCircuit.encodeNat (output z j)))) →
                            (∀ (z : List Bool), inA z ≤ inputs z) →
                              (∀ (z : List Bool) (j : Fin (outLen z)), output z j < (C z).size) →
                                (∀ (z : List Bool) (i : Fin (C z).gates.length), (C z).gates[i].args.length ≤ 2) →
                                  (∀ (z : List Bool),
                                      ∀ v < (C z).size,
                                        ∀ (b : Bool),
                                          TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                                            (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                                    (∀ (z : List Bool) (i : Fin (C z).gates.length)
                                        (a : Fin (C z).gates[i].args.length → Bool) (t : Fin (width z)),
                                        ((s z).2.1 i a).1 t =
                                          (coins z).getD
                                            (2 * bound z * width z +
                                                (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                  (2 * width z) +
                                              ↑t)
                                            false) →
                                      (∀ (z : List Bool) (i : Fin (C z).gates.length)
                                          (a : Fin (C z).gates[i].args.length → Bool) (t : Fin (width z)),
                                          ((s z).2.1 i a).2 t =
                                            (coins z).getD
                                              (2 * bound z * width z +
                                                    (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                      (2 * width z) +
                                                  width z +
                                                ↑t)
                                              false) →
                                        (∀ (z : List Bool) (i : Fin (C z).gates.length)
                                            (a : Fin (C z).gates[i].args.length → Bool)
                                            (t : Fin (C z).gates[i].args.length),
                                            ((s z).2.2 i) a t =
                                              (a t ^^ (coins z).getD (10 * bound z * width z + 2 * ↑i + ↑t) false)) →
                                          Complexity.PolyTimeComputable fun z =>
                                            Turing.pairEncode
                                              (Complexity.BinArith.encWords
                                                (List.ofFn fun i =>
                                                  Complexity.BinArith.encWords
                                                    (TCSlib.Cryptography.SecureComputation.garbledTable
                                                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂
                                                        (width z))
                                                      (C z) (s z) i)))
                                              (Turing.pairEncode
                                                (Complexity.BinArith.encWords
                                                  (List.ofFn fun v =>
                                                    List.ofFn
                                                      (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) (↑v)
                                                        ((xs z).getD (↑v) false))))
                                                (Complexity.BinArith.encWords
                                                  (List.ofFn fun j =>
                                                    Turing.pairEncode
                                                      (List.ofFn
                                                        (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z)
                                                          (output z j) false))
                                                      (List.ofFn
                                                        (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z)
                                                          (output z j) true)))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.message_poly._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.message_poly._proof_1 : ∀
  (inputs : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z)) (z : List Bool),
  ¬(C z).gates.length ≤ (C z).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.outputPairs_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.outputPairs_poly : ∀
  (width bound count inputs : List Bool → ℕ) (description coins : List Bool → List Bool),
  (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
    (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (count z) true) →
        Complexity.PolyTimeComputable description →
          Complexity.PolyTimeComputable coins →
            ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
              (s :
                (z : List Bool) →
                  TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                    ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
              (output : (z : List Bool) → Fin (count z) → ℕ),
              (∀ (z : List Bool),
                  Complexity.pairSndD (description z) =
                    Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output z j))) →
                (∀ (z : List Bool) (j : Fin (count z)), output z j < (C z).size) →
                  (∀ (z : List Bool),
                      ∀ v < (C z).size,
                        ∀ (b : Bool),
                          TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                            (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                    Complexity.PolyTimeComputable fun z =>
                      Complexity.BinArith.encWords
                        (List.ofFn fun j =>
                          Turing.pairEncode
                            (List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) (output z j) false))
                            (List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) (output z j) true)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.outputPairs_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.outputPairs_poly._proof_1_1 : ∀
  (count : List Bool → ℕ) (output : (z : List Bool) → Fin (count z) → ℕ) (z : List Bool) (j : Fin (count z)),
  ¬output z j + 1 - 1 = output z j → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.selectedKeys_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.selectedKeys_poly : ∀
  (width bound count inputs : List Bool → ℕ) (xs coins : List Bool → List Bool),
  (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
    (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (count z) true) →
        Complexity.PolyTimeComputable xs →
          Complexity.PolyTimeComputable coins →
            ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
              (s :
                (z : List Bool) →
                  TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                    ((Fin (width z) → Bool) × (Fin (width z) → Bool))),
              (∀ (z : List Bool), count z ≤ inputs z) →
                (∀ (z : List Bool),
                    ∀ v < (C z).size,
                      ∀ (b : Bool),
                        TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                          (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                  Complexity.PolyTimeComputable fun z =>
                    Complexity.BinArith.encWords
                      (List.ofFn fun v =>
                        List.ofFn
                          (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) (↑v) ((xs z).getD (↑v) false)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.selectedKeys_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram.selectedKeys_poly._proof_1_1 : ∀
  (count inputs : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z)) (z : List Bool)
  (v : Fin (count z)), count z ≤ inputs z → ¬↑v < inputs z + (C z).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.distAdv_real_ideal_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.distAdv_real_ideal_le : ∀
  (coins : Complexity.PolyExpr) (F : TCSlib.Cryptography.SecureComputation.Functionality) (n : ℕ)
  (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) {σ : Type u_1} {τ : Type u_2} {ρ : Type u_3}
  [inst : Fintype σ] [inst_1 : Fintype τ] [Nonempty τ] [inst_3 : Fintype ρ]
  (e : σ ≃ (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator coins).Coins n)
  (real : σ × τ → List Bool) (Bad : σ → Prop) (δ : ℝ),
  TCSlib.Cryptography.uprob Bad ≤ δ →
    (∀ (r : σ × τ),
        ¬Bad r.1 →
          real r =
            Turing.pairEncode
              { x := List.replicate n true, z := Turing.pairEncode (List.ofFn x) [], r := List.ofFn (e r.1),
                  received := [List.ofFn (F.f n x y).1] }.encode
              (List.ofFn (F.f n x y).2)) →
      ∀ (D : List Bool → ρ → Bool),
        TCSlib.Cryptography.distAdv real
            (F.idealA (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator coins) n x y) D ≤
          δ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.polyTimeComputable_raw`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.polyTimeComputable_raw : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw z =
    Turing.pairEncode
      (Turing.pairEncode (Complexity.NUPPT.inParam z)
        (Turing.pairEncode (Complexity.pairFstD (Complexity.NUPPT.inArg z)) []))
      (Turing.pairEncode (Complexity.NUPPT.inCoins z)
        (TCSlib.Cryptography.Strategy.encodeMsgs [Complexity.pairSndD (Complexity.NUPPT.inArg z)]))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator : Complexity.PolyExpr →
  Complexity.NUPPT
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_coins`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_coins : ∀
  (coins : Complexity.PolyExpr),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator coins).coins = coins
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_eq : ∀
  (coins : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator coins =
    Complexity.NUPPT.ofPolyTimeUniform
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.polyTimeComputable_raw coins
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_runAtL`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_runAtL : ∀
  (coins : Complexity.PolyExpr) (n : ℕ) (x f r : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator coins).runAtL n (Turing.pairEncode x f)
      r =
    { x := List.replicate n true, z := Turing.pairEncode x [], r := r, received := [f] }.encode
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_uniform`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_uniform : ∀
  (coins : Complexity.PolyExpr),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator coins).Uniform
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.statClose_real_ideal`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.statClose_real_ideal : ∀
  (coins : Complexity.PolyExpr) (F : TCSlib.Cryptography.SecureComputation.Functionality) (n : ℕ)
  (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) {σ : Type u_1} {τ : Type u_2} [inst : Fintype σ]
  [inst_1 : Fintype τ] [Nonempty τ]
  (e : σ ≃ (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator coins).Coins n)
  (real : σ × τ → List Bool) (Bad : σ → Prop) (δ : ℝ),
  TCSlib.Cryptography.uprob Bad ≤ δ →
    (∀ (r : σ × τ),
        ¬Bad r.1 →
          real r =
            Turing.pairEncode
              { x := List.replicate n true, z := Turing.pairEncode (List.ofFn x) [], r := List.ofFn (e r.1),
                  received := [List.ofFn (F.f n x y).1] }.encode
              (List.ofFn (F.f n x y).2)) →
      TCSlib.Cryptography.StatClose real
        (F.idealA (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator coins) n x y) δ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceStatistical.distAdv_real_ideal_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceStatistical.distAdv_real_ideal_le : ∀
  (H : TCSlib.Cryptography.SecureComputation.HybridProtocol TCSlib.Cryptography.SecureComputation.otFunctionality)
  (F : TCSlib.Cryptography.SecureComputation.Functionality) (p : Complexity.PolyExpr),
  H.main.P.coins = p →
    H.main.rounds = Complexity.PolyExpr.const 2 →
      H.main.verifierFirst = false →
        ∀ (BadWord : ℕ → List Bool → Prop) (δ : ℕ → ℝ),
          (∀ (n : ℕ), (TCSlib.Cryptography.uprob fun r => BadWord n (List.ofFn r)) ≤ δ n) →
            (∀ (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
                List.ofFn (F.f n x y).1 = List.ofFn (F.f n x y).2) →
              (∀ (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n),
                  ¬BadWord n (List.ofFn r.1) →
                    H.main.outV H.main.P (List.replicate n true)
                        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
                        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r =
                      List.ofFn (F.f n x y).2) →
                ∀ (D : Complexity.NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
                  TCSlib.Cryptography.distAdv (H.realA F n x y)
                      (F.idealA (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator p) n x y)
                      (D.distinguisherL n) ≤
                    δ n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord : (List Bool → List Bool) →
  (List Bool → List Bool) →
    (List Bool → ℕ) →
      (List Bool → ℕ) → (List Bool → ℕ) → (List Bool → List Bool) → (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord_eq : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord E₁ E₂ width bound inputs gates coins z =
    Complexity.BinArith.encWords
      (List.map
        (fun i =>
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord E₁ E₂ width bound inputs gates coins
            (Turing.pairEncode (List.replicate i true) z))
        (List.range (Complexity.BinArith.decWords (gates z)).length))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord_garbledTables`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord_garbledTables : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
  (gateCode : BoolCircuit.DAGGate → List Bool) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z))
  (s :
    TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool))),
  gates z = Complexity.BinArith.encWords (List.map gateCode C.gates) →
    (∀ (i : Fin C.gates.length),
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord E₁ E₂ width bound inputs gates coins
            (Turing.pairEncode (List.replicate (↑i) true) z) =
          Complexity.BinArith.encWords
            (TCSlib.Cryptography.SecureComputation.garbledTable
              (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)) C s i)) →
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord E₁ E₂ width bound inputs gates coins
          z =
        Complexity.BinArith.encWords
          (List.ofFn fun i =>
            Complexity.BinArith.encWords
              (TCSlib.Cryptography.SecureComputation.garbledTable
                (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)) C s i))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ {width bound inputs : List Bool → ℕ} {gates coins : List Bool → List Bool},
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              Complexity.PolyTimeComputable gates →
                Complexity.PolyTimeComputable coins →
                  Complexity.PolyTimeComputable
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.allTablesWord E₁ E₂ width bound
                      inputs gates coins)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord : (List Bool → List Bool) →
  (List Bool → List Bool) →
    (List Bool → ℕ) →
      (List Bool → ℕ) → (List Bool → ℕ) → (List Bool → List Bool) → (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord_eq : ∀ (E₁ E₂ : List Bool → List Bool)
  (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool) (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord E₁ E₂ width bound inputs gates coins w =
    have record := fun v =>
      Complexity.BinArith.getW (Turing.pairEncode (Complexity.pairFstD v) (gates (Complexity.pairSndD v)));
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord E₁ E₂
      (fun v => width (Complexity.pairSndD v)) (fun v => bound (Complexity.pairSndD v))
      (fun v => inputs (Complexity.pairSndD v)) (fun v => (Complexity.pairFstD v).length)
      (fun v => Complexity.pairFstD (record v)) (fun v => Complexity.pairSndD (record v))
      (fun v => coins (Complexity.pairSndD v)) w
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord_pair`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord_pair : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool) (i : ℕ)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord E₁ E₂ width bound inputs gates coins
      (Turing.pairEncode (List.replicate i true) z) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord E₁ E₂ width bound inputs (fun x => i)
      (fun v => Complexity.pairFstD (Complexity.BinArith.getW (Turing.pairEncode (List.replicate i true) (gates v))))
      (fun v => Complexity.pairSndD (Complexity.BinArith.getW (Turing.pairEncode (List.replicate i true) (gates v))))
      coins z
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ {width bound inputs : List Bool → ℕ} {gates coins : List Bool → List Bool},
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              Complexity.PolyTimeComputable gates →
                Complexity.PolyTimeComputable coins →
                  Complexity.PolyTimeComputable
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables.entryWord E₁ E₂ width bound inputs
                      gates coins)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.length_outputWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.length_outputWord : ∀ (p : Complexity.PolyExpr)
  (z : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord p z).length =
    p.eval (Complexity.pairFstD z).length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit : List Bool → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit z =
    have ctx := Complexity.pairFstD z;
    have j := Complexity.pairSndD z;
    have vals := Complexity.pairFstD (Complexity.pairSndD ctx);
    have pairs := Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD ctx));
    have outs := Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD ctx));
    have v := Complexity.BinArith.uHead (Complexity.BinArith.getW (Turing.pairEncode j outs));
    have k :=
      TCSlib.Cryptography.EnsembleLemmas.padL (Complexity.pairFstD ctx).length
        (Complexity.BinArith.getW (Turing.pairEncode v vals));
    have p := Complexity.BinArith.getW (Turing.pairEncode j pairs);
    if k = Complexity.pairFstD p then false else decide (k = Complexity.pairSndD p)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit_layout : ∀ {n k : ℕ}
  (vs : List (Fin n → Bool)) (ps : List (List Bool)) (outs : Fin k → ℕ) (j : Fin k),
  outs j < vs.length →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit
        (Turing.pairEncode
          (Turing.pairEncode (List.replicate n true)
            (Turing.pairEncode (Complexity.BinArith.encWords (List.map List.ofFn vs))
              (Turing.pairEncode (Complexity.BinArith.encWords ps)
                (Complexity.BinArith.encWords (List.ofFn fun i => BoolCircuit.encodeNat (outs i))))))
          (List.replicate (↑j) true)) =
      if List.ofFn (vs.getD (outs j) default) = Complexity.pairFstD (ps.getD ↑j []) then false
      else decide (List.ofFn (vs.getD (outs j) default) = Complexity.pairSndD (ps.getD ↑j []))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit_poly : Complexity.PolyTimeComputable
  fun z => [TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit z]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord : Complexity.PolyExpr →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord_eq : ∀ (p : Complexity.PolyExpr)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord p z =
    List.ofFn fun j =>
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit
        (Turing.pairEncode z (List.replicate (↑j) true))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord_getD`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord_getD : ∀ (p : Complexity.PolyExpr)
  (z : List Bool) (j : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord p z).getD j false =
    if j < p.eval (Complexity.pairFstD z).length then
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputBit (Turing.pairEncode z (List.replicate j true))
    else false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord_layout : ∀ (p : Complexity.PolyExpr)
  {n : ℕ} (vs : List (Fin n → Bool)) (ps : List (List Bool)) (outs : Fin (p.eval n) → ℕ),
  (∀ (j : Fin (p.eval n)), outs j < vs.length) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord p
        (Turing.pairEncode (List.replicate n true)
          (Turing.pairEncode (Complexity.BinArith.encWords (List.map List.ofFn vs))
            (Turing.pairEncode (Complexity.BinArith.encWords ps)
              (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (outs j)))))) =
      List.ofFn fun j =>
        if List.ofFn (vs.getD (outs j) default) = Complexity.pairFstD (ps.getD ↑j []) then false
        else decide (List.ofFn (vs.getD (outs j) default) = Complexity.pairSndD (ps.getD ↑j []))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord_poly : ∀ (p : Complexity.PolyExpr),
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO.outputWord p)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry z =
    have ctx := Complexity.pairSndD z;
    have N := Complexity.pairFstD ctx;
    have A := Complexity.pairFstD (Complexity.pairSndD ctx);
    have msg := Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD ctx)));
    have ans := Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD ctx)));
    if (Complexity.pairFstD z).length < A.length then
      TCSlib.Cryptography.EnsembleLemmas.padL N.length
        (Complexity.BinArith.getW
          (Turing.pairEncode (Complexity.pairFstD z)
            (Complexity.BinArith.encWords
              (Complexity.BinArith.decWords (Complexity.pairFstD (Complexity.pairSndD msg))))))
    else List.ofFn fun t => ans.getD (((Complexity.pairFstD z).length - A.length) * N.length + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry_layout : ∀ (N A B msg ans : List Bool)
  (v : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry
      (Turing.pairEncode (List.replicate v true)
        (Turing.pairEncode N (Turing.pairEncode A (Turing.pairEncode B (Turing.pairEncode msg ans))))) =
    if v < A.length then
      List.ofFn
        (TCSlib.Cryptography.padFin N.length
          ((Complexity.BinArith.decWords (Complexity.pairFstD (Complexity.pairSndD msg))).getD v []))
    else List.ofFn fun t => ans.getD ((v - A.length) * N.length + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry_layout._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry_layout._simp_1_1 : ∀ (k : ℕ)
  (a : List Bool), TCSlib.Cryptography.EnsembleLemmas.padL k a = List.ofFn (TCSlib.Cryptography.padFin k a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry_poly : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords z =
    Complexity.BinArith.encWords
      (List.map
        (fun v =>
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initEntry
            (Turing.pairEncode (List.replicate v true) z))
        (List.range
          ((Complexity.pairFstD (Complexity.pairSndD z)).length +
            (Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD z))).length)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords_layout : ∀ (N A B msg ans : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords
      (Turing.pairEncode N (Turing.pairEncode A (Turing.pairEncode B (Turing.pairEncode msg ans)))) =
    Complexity.BinArith.encWords
      (List.ofFn fun v =>
        if ↑v < A.length then
          List.ofFn
            (TCSlib.Cryptography.padFin N.length
              ((Complexity.BinArith.decWords (Complexity.pairFstD (Complexity.pairSndD msg))).getD ↑v []))
        else List.ofFn fun t => ans.getD ((↑v - A.length) * N.length + ↑t) false)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords_poly : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobProgram.output_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobProgram.output_poly : ∀
  (inA inB outLen : Complexity.PolyExpr) (circ : (n : ℕ) → BoolCircuit.DAGCircuit (inA.eval n + inB.eval n))
  (outs : (n : ℕ) → Fin (outLen.eval n) → ℕ),
  (∀ (n : ℕ) (j : Fin (outLen.eval n)), outs n j < (circ n).size) →
    ∀ {gen E₁ E₂ N msg ans : List Bool → List Bool},
      Complexity.PolyTimeComputable gen →
        (∀ (n : ℕ),
            gen (List.replicate n true) =
              Turing.pairEncode (circ n).encode
                (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (outs n j)))) →
          Complexity.PolyTimeComputable E₁ →
            Complexity.PolyTimeComputable E₂ →
              Complexity.PolyTimeComputable N →
                Complexity.PolyTimeComputable msg →
                  Complexity.PolyTimeComputable ans →
                    ∀ (init : (z : List Bool) → List (Fin (N z).length → Bool)) (T : List Bool → ℕ → List (List Bool))
                      (pairs : List Bool → List (List Bool)),
                      (∀ (z : List Bool),
                          Complexity.BinArith.encWords (List.map List.ofFn (init z)) =
                            TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit.initWords
                              (Turing.pairEncode (List.replicate (N z).length true)
                                (Turing.pairEncode (List.replicate (inA.eval (N z).length) true)
                                  (Turing.pairEncode (List.replicate (inB.eval (N z).length) true)
                                    (Turing.pairEncode (msg z) (ans z)))))) →
                        (∀ (z : List Bool), (init z).length = inA.eval (N z).length + inB.eval (N z).length) →
                          (∀ (z : List Bool) (v : ℕ),
                              T z v =
                                if inA.eval (N z).length + inB.eval (N z).length ≤ v then
                                  Complexity.BinArith.decWords
                                    ((Complexity.BinArith.decWords (Complexity.pairFstD (msg z))).getD
                                      (v - (inA.eval (N z).length + inB.eval (N z).length)) [])
                                else []) →
                            (∀ (z : List Bool),
                                pairs z =
                                  Complexity.BinArith.decWords (Complexity.pairSndD (Complexity.pairSndD (msg z)))) →
                              Complexity.PolyTimeComputable fun z =>
                                have vals :=
                                  BoolCircuit.runWith
                                    (fun g vs =>
                                      TCSlib.Cryptography.SecureComputation.evalGate
                                        (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (N z).length) (T z)
                                        vs.length g vs)
                                    (circ (N z).length).gates (init z);
                                List.ofFn fun j =>
                                  if
                                      List.ofFn (vals.getD (outs (N z).length j) default) =
                                        Complexity.pairFstD ((pairs z).getD ↑j []) then
                                    false
                                  else
                                    decide
                                      (List.ofFn (vals.getD (outs (N z).length j) default) =
                                        Complexity.pairSndD ((pairs z).getD ↑j []))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.idealB_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.idealB_eq : ∀
  {fakeMessage activeAnswers : List Bool → List Bool} (hM : Complexity.PolyTimeComputable fakeMessage)
  (hA : Complexity.PolyTimeComputable activeAnswers) (coins : Complexity.PolyExpr)
  (F : TCSlib.Cryptography.SecureComputation.Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
  (y : Fin (F.inB.eval n) → Bool)
  (r : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins).Coins n),
  F.idealB (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins) n x y r =
    have w :=
      Complexity.NUPPT.layout (List.replicate n true) (Turing.pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) []
        (List.ofFn r);
    Turing.pairEncode
      { x := List.replicate n true, z := Turing.pairEncode (List.ofFn y) (activeAnswers w), r := [],
          received := [fakeMessage w] }.encode
      (List.ofFn (F.f n x y).1)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw : (List Bool → List Bool) →
  (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw_eq : ∀
  (fakeMessage activeAnswers : List Bool → List Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw fakeMessage activeAnswers z =
    { x := Complexity.NUPPT.inParam z,
        z := Turing.pairEncode (Complexity.pairFstD (Complexity.NUPPT.inArg z)) (activeAnswers z), r := [],
        received := [fakeMessage z] }.encode
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw_poly : ∀
  {fakeMessage activeAnswers : List Bool → List Bool},
  Complexity.PolyTimeComputable fakeMessage →
    Complexity.PolyTimeComputable activeAnswers →
      Complexity.PolyTimeComputable
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw fakeMessage activeAnswers)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator : {fakeMessage activeAnswers :
    List Bool → List Bool} →
  Complexity.PolyTimeComputable fakeMessage →
    Complexity.PolyTimeComputable activeAnswers → Complexity.PolyExpr → Complexity.NUPPT
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator.congr_simp`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator.congr_simp : ∀
  {fakeMessage fakeMessage_1 : List Bool → List Bool} (e_fakeMessage : fakeMessage = fakeMessage_1)
  {activeAnswers activeAnswers_1 : List Bool → List Bool} (e_activeAnswers : activeAnswers = activeAnswers_1)
  (hM : Complexity.PolyTimeComputable fakeMessage) (hA : Complexity.PolyTimeComputable activeAnswers)
  (coins coins_1 : Complexity.PolyExpr),
  coins = coins_1 →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator ⋯ ⋯ coins_1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_coins`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_coins : ∀
  {fakeMessage activeAnswers : List Bool → List Bool} (hM : Complexity.PolyTimeComputable fakeMessage)
  (hA : Complexity.PolyTimeComputable activeAnswers) (coins : Complexity.PolyExpr),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins).coins = coins
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_eq : ∀
  {fakeMessage activeAnswers : List Bool → List Bool} (hM : Complexity.PolyTimeComputable fakeMessage)
  (hA : Complexity.PolyTimeComputable activeAnswers) (coins : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins =
    Complexity.NUPPT.ofPolyTimeUniform ⋯ coins
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_runAt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_runAt : ∀
  {fakeMessage activeAnswers : List Bool → List Bool} (hM : Complexity.PolyTimeComputable fakeMessage)
  (hA : Complexity.PolyTimeComputable activeAnswers) (coins : Complexity.PolyExpr) (n : ℕ) (y f : List Bool)
  (r : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins).Coins n),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins).runAt n
      (Turing.pairEncode y f) r =
    have w := Complexity.NUPPT.layout (List.replicate n true) (Turing.pairEncode y f) [] (List.ofFn r);
    { x := List.replicate n true, z := Turing.pairEncode y (activeAnswers w), r := [],
        received := [fakeMessage w] }.encode
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_runAtL`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_runAtL : ∀
  {fakeMessage activeAnswers : List Bool → List Bool} (hM : Complexity.PolyTimeComputable fakeMessage)
  (hA : Complexity.PolyTimeComputable activeAnswers) (coins : Complexity.PolyExpr) (n : ℕ) (y f r : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins).runAtL n
      (Turing.pairEncode y f) r =
    have w := Complexity.NUPPT.layout (List.replicate n true) (Turing.pairEncode y f) [] r;
    { x := List.replicate n true, z := Turing.pairEncode y (activeAnswers w), r := [],
        received := [fakeMessage w] }.encode
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_uniform`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator_uniform : ∀
  {fakeMessage activeAnswers : List Bool → List Bool} (hM : Complexity.PolyTimeComputable fakeMessage)
  (hA : Complexity.PolyTimeComputable activeAnswers) (coins : Complexity.PolyExpr),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator hM hA coins).Uniform
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStageZero.acceptProb_eq_stage0`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStageZero.acceptProb_eq_stage0 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (S n : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    ∀ (v : ℕ → Bool),
      C.size ≤ S →
        ∀
          (seed :
            List Bool →
              TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
          (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
              (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
            (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
                ((seed q).2.1 i a).1 t =
                  q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
                    false) →
              (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
                  ((seed q).2.1 i a).2 t =
                    q.getD
                      (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n +
                        ↑t)
                      false) →
                (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool)
                    (t : Fin C.gates[i].args.length),
                    ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
                  ∀
                    (M :
                      TCSlib.Cryptography.SecureComputation.MultiEnc (Fin n → Bool) (List Bool)
                        ((Fin n → Bool) × (Fin n → Bool)))
                    (inA inB outLen : ℕ) (output : Fin outLen → ℕ)
                    (H :
                      TCSlib.Cryptography.SecureComputation.HybridProtocol
                        TCSlib.Cryptography.SecureComputation.otFunctionality)
                    (first : ℕ → List Bool → List Bool → List Bool),
                    H.main.rounds = Complexity.PolyExpr.const 2 →
                      H.main.verifierFirst = false →
                        H.main.V.coins = Complexity.PolyExpr.const 0 →
                          (∀ (w z r : List Bool), H.main.P.next w z r [] = first w.length (Complexity.pairFstD z) r) →
                            ∀ (xs ys aliceOutput : List Bool),
                              H.main.P.coinLen (List.replicate n true).length = 10 * S * n + 2 * S →
                                H.calls.eval n = inB * n →
                                  (∀ (i : Fin inB), v (inA + ↑i) = ys.getD (↑i) false) →
                                    (∀ (rA rB : List Bool) (i : Fin inB) (t : Fin n),
                                        (H.answersB n xs ys rA rB).getD (↑i * n + ↑t) false =
                                          TCSlib.Cryptography.SecureComputation.keyAt C (seed rA) (inA + ↑i)
                                            (ys.getD (↑i) false) t) →
                                      (∀ (r : List Bool),
                                          first n xs r =
                                            Turing.pairEncode
                                              (Complexity.BinArith.encWords
                                                (List.ofFn fun i =>
                                                  Complexity.BinArith.encWords
                                                    (TCSlib.Cryptography.SecureComputation.garbledTable M C (seed r)
                                                      i)))
                                              (Turing.pairEncode
                                                (Complexity.BinArith.encWords
                                                  (List.ofFn fun w =>
                                                    List.ofFn
                                                      (TCSlib.Cryptography.SecureComputation.keyAt C (seed r) (↑w)
                                                        (v ↑w))))
                                                (Complexity.BinArith.encWords
                                                  (List.ofFn fun j =>
                                                    Turing.pairEncode
                                                      (List.ofFn
                                                        (TCSlib.Cryptography.SecureComputation.keyAt C (seed r)
                                                          (output j) false))
                                                      (List.ofFn
                                                        (TCSlib.Cryptography.SecureComputation.keyAt C (seed r)
                                                          (output j) true)))))) →
                                        ∀ {κ : Type u_1} [inst : Fintype κ] (D : List Bool → κ → Bool),
                                          TCSlib.Cryptography.acceptProb
                                              (fun r =>
                                                Turing.pairEncode
                                                  (H.main.viewV (List.replicate n true)
                                                      (H.privA n xs ys (List.ofFn r.1) (List.ofFn r.2))
                                                      (H.privB n xs ys (List.ofFn r.1) (List.ofFn r.2)) r).encode
                                                  aliceOutput)
                                              D =
                                            TCSlib.Cryptography.acceptProb
                                              (fun r =>
                                                TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                                                  M C (seed (List.ofFn r)) inA inB outLen output v
                                                  (List.replicate n true) ys [] aliceOutput 0)
                                              D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStatistical.statClose_real_output_switch`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStatistical.statClose_real_output_switch : ∀
  {G : TCSlib.Cryptography.SecureComputation.Functionality} (H : TCSlib.Cryptography.SecureComputation.HybridProtocol G)
  (F : TCSlib.Cryptography.SecureComputation.Functionality) (p : Complexity.PolyExpr),
  H.main.P.coins = p →
    ∀ (BadWord : ℕ → List Bool → Prop) (δ : ℕ → ℝ),
      (∀ (n : ℕ), (TCSlib.Cryptography.uprob fun r => BadWord n (List.ofFn r)) ≤ δ n) →
        (∀ (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n),
            ¬BadWord n (List.ofFn r.1) →
              H.main.outP (List.replicate n true)
                  (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
                  (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r =
                List.ofFn (F.f n x y).1) →
          ∀ (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
            TCSlib.Cryptography.StatClose (H.realB F n x y)
              (fun r =>
                Turing.pairEncode
                  (H.main.viewV (List.replicate n true)
                      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
                      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
                  (List.ofFn (F.f n x y).1))
              (δ n)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector : (List Bool → List Bool) →
  (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector_eq : ∀
  (m msg : List Bool → List Bool) (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector m msg w =
    have x := Complexity.pairFstD w;
    have v := (Complexity.BinArith.decWords (Complexity.pairSndD (Complexity.pairSndD w))).length;
    if (m x).length ≤ v then
      Complexity.BinArith.encWords
        (Complexity.BinArith.decWords
          (Complexity.BinArith.getW
            (Turing.pairEncode (List.replicate (v - (m x).length) true)
              (Complexity.BinArith.encWords (Complexity.BinArith.decWords (Complexity.pairFstD (msg x)))))))
    else []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector_host`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector_host : ∀ {α : Type}
  (m msg : List Bool → List Bool) (x gate : List Bool) (vs : List α) (code : α → List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector m msg
      (Turing.pairEncode x (Turing.pairEncode gate (Complexity.BinArith.encWords (List.map code vs)))) =
    Complexity.BinArith.encWords
      (if (m x).length ≤ vs.length then
        Complexity.BinArith.decWords
          ((Complexity.BinArith.decWords (Complexity.pairFstD (msg x))).getD (vs.length - (m x).length) [])
      else [])
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector_poly : ∀
  {m msg : List Bool → List Bool},
  Complexity.PolyTimeComputable m →
    Complexity.PolyTimeComputable msg →
      Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables.tableSelector m msg)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobViewShape.encode_viewV_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobViewShape.encode_viewV_eq : ∀
  (H : TCSlib.Cryptography.SecureComputation.HybridProtocol TCSlib.Cryptography.SecureComputation.otFunctionality)
  (first : ℕ → List Bool → List Bool → List Bool),
  H.main.rounds = Complexity.PolyExpr.const 2 →
    H.main.verifierFirst = false →
      H.main.V.coins = Complexity.PolyExpr.const 0 →
        (∀ (w z r : List Bool), H.main.P.next w z r [] = first w.length (Complexity.pairFstD z) r) →
          ∀ (n : ℕ) (xs ys : List Bool) (r : H.Coins n),
            (H.main.viewV (List.replicate n true) (H.privA n xs ys (List.ofFn r.1) (List.ofFn r.2))
                  (H.privB n xs ys (List.ofFn r.1) (List.ofFn r.2)) r).encode =
              { x := List.replicate n true,
                  z := Turing.pairEncode ys (H.answersB n xs ys (List.ofFn r.1) (List.ofFn r.2)), r := [],
                  received := [first n xs (List.ofFn r.1)] }.encode
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CallEquations.inputA_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CallEquations.inputA_eq : ∀ (A S : Complexity.PolyExpr)
  (n m : ℕ) (x r : List Bool) (call : Fin (m * n) → Fin 2 → Bool),
  (∀ (i : Fin m) (t : Fin n) (c : Fin 2),
      call (finProdFinEquiv (i, t)) c = r.getD (((decide (↑c = 1)).toNat * S.eval n + A.eval n + ↑i) * n + ↑t) false) →
    ∀ (j : Fin (m * n)),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA A S
          (Turing.pairEncode (List.replicate n true)
            (Turing.pairEncode x (Turing.pairEncode r (List.replicate (↑j) true)))) =
        List.ofFn (call j)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CallEquations.inputB_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CallEquations.inputB_eq : ∀ (n m : ℕ) (x r : List Bool)
  (call : Fin (m * n) → Fin 1 → Bool),
  (∀ (i : Fin m) (t : Fin n) (c : Fin 1), call (finProdFinEquiv (i, t)) c = x.getD (↑i) false) →
    ∀ (j : Fin (m * n)),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB
          (Turing.pairEncode (List.replicate n true)
            (Turing.pairEncode x (Turing.pairEncode r (List.replicate (↑j) true)))) =
        List.ofFn (call j)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CallEquations.inputB_eq._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CallEquations.inputB_eq._proof_1_1 : ∀ (n : ℕ) (t : Fin n),
  ↑t < n → ¬0 < n → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase : Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
    Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit_eq : ∀
  (o : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool) (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit o w =
    if Complexity.pairSndD w = [] then []
    else
      o (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase (Complexity.pairFstD w))
        ((Complexity.pairSndD w).headD false)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit_pair`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit_pair : ∀
  (o : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool)
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit o
      (Turing.pairEncode (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode q) w) =
    if w = [] then [] else o q (w.headD false)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit_poly : ∀
  (o : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool),
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit o)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.flatMap_scan`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.flatMap_scan : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (o : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool) (N : ℕ)
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) (w : List Bool),
  w.length ≤ N →
    List.flatMap
        (fun i =>
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.emit o
            ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ)^[i]
              (Turing.pairEncode (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode q) w)))
        (List.range N) =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan δ o q w
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.flatMap_scan._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.flatMap_scan._proof_1_1 : ∀ (w : List Bool),
  w.length ≤ 0 → ¬w.length = 0 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.flatMap_scan._simp_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.flatMap_scan._simp_1_2 : ∀ {α : Type u_1}
  (a : α) (l : List α), (a :: l = []) = False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_iterate`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_iterate : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (w : List Bool) (i : ℕ),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ)^[i] w).length ≤ 9 * (w.length + 1)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_iterate._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_iterate._proof_1_1 : ∀ (w : List Bool),
  ¬w.length ≤ 9 * (w.length + 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_iterate._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_iterate._proof_1_2 : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (w : List Bool) (i : ℕ),
  (Complexity.pairSndD ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ)^[i] w)).length ≤
      w.length →
    ¬2 * 3 + 2 +
            ((Complexity.pairSndD
                  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ)^[i] w)).length -
              1) ≤
          9 * (w.length + 1) →
      False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_phaseCode`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_phaseCode : ∀
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode q).length = 3
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_snd_iterate`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_snd_iterate : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (w : List Bool) (i : ℕ),
  (Complexity.pairSndD ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ)^[i] w)).length ≤
    w.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_snd_step`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_snd_step : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (w : List Bool),
  (Complexity.pairSndD (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ w)).length ≤
    (Complexity.pairSndD w).length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_snd_step._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.length_snd_step._proof_1_1 : ∀
  (w : List Bool), ¬(Complexity.pairSndD w).length - 1 ≤ (Complexity.pairSndD w).length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
  List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode_eq : ∀
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode q = [q.1, q.2.1, q.2.2]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phase_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phase_eq : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase =
  (Bool × Bool × Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase : List Bool →
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase_code`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase_code : ∀
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode q) =
    q
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase_eq : ∀ (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase w =
    (w.headD false, (List.drop 1 w).headD false, (List.drop 2 w).headD false)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
    Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) →
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan._sunfold`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan._sunfold : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
    Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) →
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan._unsafe_rec`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan._unsafe_rec : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
    Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) →
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan.match_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan.match_1 : (motive :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → List Bool → Sort u_1) →
  (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) →
    (x_1 : List Bool) →
      ((x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) → motive x []) →
        ((q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) →
            (b : Bool) → (w : List Bool) → motive q (b :: w)) →
          motive x x_1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_cons`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_cons : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (o : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool)
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) (b : Bool) (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan δ o q (b :: w) =
    o q b ++ TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan δ o (δ q b) w
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_host`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_host : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (o : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool)
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase),
  ∃ M A d,
    (Turing.ModuleHost.Clean M (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan δ o q)
        (fun x => []) fun n => A * (n + 1) ^ d) ∧
      ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
        |(Turing.MultiTapeTM.runFrom (Turing.Cfg.ofWords M.tm.q₀ (Turing.stateWord M.k arg)) v).workTapePos j| ≤
          ↑(A * (arg.length + 1) ^ d)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_nil`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_nil : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (o : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool)
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan δ o q [] = []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_poly : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (o : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → List Bool)
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase),
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan δ o q)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan_poly._proof_1_1 : ∀
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) (w : List Bool),
  ¬w.length ≤
        2 * (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode q).length + 2 + w.length + 1 +
          1 →
    False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
    Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step_eq : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ w =
    Turing.pairEncode
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode
        (δ (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.readPhase (Complexity.pairFstD w))
          ((Complexity.pairSndD w).headD false)))
      (List.drop 1 (Complexity.pairSndD w))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step_pair`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step_pair : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase)
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ
      (Turing.pairEncode (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode q) w) =
    Turing.pairEncode
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.phaseCode (δ q (w.headD false)))
      (List.drop 1 w)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step_poly : ∀
  (δ :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
      Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase),
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.step δ)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling.assignmentIndex_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling.assignmentIndex_poly : ∀
  {b₀ b₁ : List Bool → Bool},
  (Complexity.PolyTimeComputable fun z => [b₀ z]) →
    (Complexity.PolyTimeComputable fun z => [b₁ z]) →
      Complexity.PolyTimeComputable fun z => List.replicate ((b₀ z).toNat + 2 * (b₁ z).toNat) true
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling.keyWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling.keyWord_poly : ∀
  {coins : List Bool → List Bool} {width bound vertex : List Bool → ℕ} {bit : List Bool → Bool}
  {key : (z : List Bool) → Fin (width z) → Bool},
  Complexity.PolyTimeComputable coins →
    (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
        (Complexity.PolyTimeComputable fun z => List.replicate (vertex z) true) →
          (Complexity.PolyTimeComputable fun z => [bit z]) →
            (∀ (z : List Bool) (t : Fin (width z)),
                key z t = (coins z).getD (((bit z).toNat * bound z + vertex z) * width z + ↑t) false) →
              Complexity.PolyTimeComputable fun z => List.ofFn (key z)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling.rowCoinWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling.rowCoinWord_poly : ∀
  {coins : List Bool → List Bool} {width bound gate index : List Bool → ℕ}
  {nonce : (z : List Bool) → Fin (width z) → Bool} (half : Bool),
  Complexity.PolyTimeComputable coins →
    (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
        (Complexity.PolyTimeComputable fun z => List.replicate (gate z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (index z) true) →
            (∀ (z : List Bool) (t : Fin (width z)),
                nonce z t =
                  (coins z).getD
                    (2 * bound z * width z + (4 * gate z + index z) * (2 * width z) + half.toNat * width z + ↑t)
                    false) →
              Complexity.PolyTimeComputable fun z => List.ofFn (nonce z)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling.shiftBit_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling.shiftBit_poly : ∀
  {coins : List Bool → List Bool} {width bound gate : List Bool → ℕ} (j : ℕ),
  Complexity.PolyTimeComputable coins →
    (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
        (Complexity.PolyTimeComputable fun z => List.replicate (gate z) true) →
          Complexity.PolyTimeComputable fun z => [(coins z).getD (10 * bound z * width z + 2 * gate z + j) false]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks : ℕ → ℕ → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks_eq : ∀ (S n : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks S n =
    ((Bool → Fin S → Fin n → Bool) × (Fin S → Fin 4 → Fin (2 * n) → Bool) × (Fin S → Fin 2 → Bool))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel : (S n : ℕ) →
  (Fin S → Bool) →
    (Fin S → Equiv.Perm (Fin 4)) →
      (Fin S → Fin 2 → Bool) → Equiv.Perm (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks S n)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel_eq : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (q : TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks S n),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel S n values rows mask) q =
    ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel S n values) q.1,
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel S n rows) q.2.1,
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel S mask) q.2.2)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv : (S n : ℕ) →
  (Fin (10 * S * n + 2 * S) → Bool) ≃ TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks S n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_eq : ∀ (S n : ℕ)
  (r : Fin (10 * S * n + 2 * S) → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r =
    (fun b v t => (List.ofFn r).getD ((b.toNat * S + ↑v) * n + ↑t) false, fun i a t =>
      (List.ofFn r).getD (2 * S * n + (4 * ↑i + ↑a) * (2 * n) + ↑t) false, fun i t =>
      (List.ofFn r).getD (10 * S * n + 2 * ↑i + ↑t) false)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_key : ∀ (S n : ℕ)
  (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r).1 b v t =
    (List.ofFn r).getD ((b.toNat * S + ↑v) * n + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_row : ∀ (S n : ℕ)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n)),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r).2.1 i a t =
    (List.ofFn r).getD (2 * S * n + (4 * ↑i + ↑a) * (2 * n) + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_shift`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_shift : ∀ (S n : ℕ)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r).2.2 i t =
    (List.ofFn r).getD (10 * S * n + 2 * ↑i + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel : (S n : ℕ) →
  (Fin S → Bool) → Equiv.Perm (Bool → Fin S → Fin n → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel._proof_1 : ∀ (S n : ℕ)
  (values : Fin S → Bool) (k : Bool → Fin S → Fin n → Bool), (fun b v t => k (b ^^ values v ^^ values v) v t) = k
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel_eq : ∀ (S n : ℕ)
  (values : Fin S → Bool) (k : Bool → Fin S → Fin n → Bool) (b : Bool) (v : Fin S) (t : Fin n),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel S n values) k b v t =
    k (b ^^ values v) v t
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel : (S n : ℕ) →
  (Fin S → Bool) → (Fin S → Equiv.Perm (Fin 4)) → (Fin S → Fin 2 → Bool) → Equiv.Perm (Fin (10 * S * n + 2 * S) → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_blocks`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_blocks : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n)
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r) =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel S n values rows mask)
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_eq : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n).symm
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel S n values rows mask)
        ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n)
          ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).1
      b v t =
    ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r).1 (b ^^ values v) v t
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key_fixed`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key_fixed : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n),
  values v = false →
    (List.ofFn ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).getD
        ((b.toNat * S + ↑v) * n + ↑t) false =
      (List.ofFn r).getD ((b.toNat * S + ↑v) * n + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key_getD`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key_getD : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n),
  (List.ofFn ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).getD
      ((b.toNat * S + ↑v) * n + ↑t) false =
    (List.ofFn r).getD (((b ^^ values v).toNat * S + ↑v) * n + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n)),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n)
            ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).2.1
      i a t =
    ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r).2.1 i ((rows i) a) t
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row_fixed`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row_fixed : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n)),
  (rows i) a = a →
    (List.ofFn ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).getD
        (2 * S * n + (4 * ↑i + ↑a) * (2 * n) + ↑t) false =
      (List.ofFn r).getD (2 * S * n + (4 * ↑i + ↑a) * (2 * n) + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row_getD`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row_getD : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n)),
  (List.ofFn ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).getD
      (2 * S * n + (4 * ↑i + ↑a) * (2 * n) + ↑t) false =
    (List.ofFn r).getD (2 * S * n + (4 * ↑i + ↑((rows i) a)) * (2 * n) + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n)
            ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).2.2
      i t =
    (((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r).2.2 i t ^^ mask i t)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift_fixed`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift_fixed : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2),
  mask i t = false →
    (List.ofFn ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).getD
        (10 * S * n + 2 * ↑i + ↑t) false =
      (List.ofFn r).getD (10 * S * n + 2 * ↑i + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift_getD`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift_getD : ∀ (S n : ℕ)
  (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2),
  (List.ofFn ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n values rows mask) r)).getD
      (10 * S * n + 2 * ↑i + ↑t) false =
    ((List.ofFn r).getD (10 * S * n + 2 * ↑i + ↑t) false ^^ mask i t)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel : (S n : ℕ) →
  (Fin S → Equiv.Perm (Fin 4)) → Equiv.Perm (Fin S → Fin 4 → Fin (2 * n) → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel_eq : ∀ (S n : ℕ)
  (rows : Fin S → Equiv.Perm (Fin 4)) (k : Fin S → Fin 4 → Fin (2 * n) → Bool) (i : Fin S) (a : Fin 4)
  (t : Fin (2 * n)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel S n rows) k i a t = k i ((rows i) a) t
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel : (S : ℕ) →
  (Fin S → Fin 2 → Bool) → Equiv.Perm (Fin S → Fin 2 → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel_eq : ∀ (S : ℕ)
  (mask k : Fin S → Fin 2 → Bool) (i : Fin S) (t : Fin 2),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel S mask) k i t = (k i t ^^ mask i t)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape : (S n : ℕ) →
  (Fin (10 * S * n + 2 * S) → Bool) ≃ (Fin (2 * S * n) → Bool) × (Fin (S * 4 * (2 * n)) → Bool) × (Fin (S * 2) → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape._proof_1 : ∀ (S n : ℕ),
  10 * S * n + 2 * S = 2 * S * n + (S * 4 * (2 * n) + S * 2)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_eq : ∀ (S n : ℕ)
  (r : Fin (10 * S * n + 2 * S) → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape S n) r =
    (fun i => (List.ofFn r).getD (↑i) false, fun i => (List.ofFn r).getD (2 * S * n + ↑i) false, fun i =>
      (List.ofFn r).getD (10 * S * n + ↑i) false)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_key : ∀ (S n : ℕ)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin (2 * S * n)),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape S n) r).1 i =
    (List.ofFn r).getD (↑i) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_key._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_key._proof_1_1 : ∀ (S n : ℕ)
  (i : Fin (2 * S * n)),
  10 * S * n + 2 * S = 2 * S * n + (S * 4 * (2 * n) + S * 2) → ↑i < 2 * S * n → ¬↑i < 10 * S * n + 2 * S → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_row : ∀ (S n : ℕ)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin (S * 4 * (2 * n))),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape S n) r).2.1 i =
    (List.ofFn r).getD (2 * S * n + ↑i) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_row._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_row._proof_1_1 : ∀ (S n : ℕ)
  (i : Fin (S * 4 * (2 * n))),
  10 * S * n + 2 * S = 2 * S * n + (S * 4 * (2 * n) + S * 2) →
    ↑i < S * 4 * (2 * n) → ¬2 * S * n + ↑i < 10 * S * n + 2 * S → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_shift`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_shift : ∀ (S n : ℕ)
  (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin (S * 2)),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape S n) r).2.2 i =
    (List.ofFn r).getD (10 * S * n + ↑i) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_shift._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_shift._proof_1_1 : ∀ (S n : ℕ)
  (i : Fin (S * 2)), ↑i < S * 2 → ¬10 * S * n + ↑i < 10 * S * n + 2 * S → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding : (l : ℕ) →
  l ≤ 2 → (Fin l → Bool) ↪ Fin 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding._proof_1 : ∀ (l : ℕ)
  (hl : l ≤ 2) (x x_1 : Fin l → Bool),
  ⟨List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn x), ⋯⟩ =
      ⟨List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn x_1), ⋯⟩ →
    x = x_1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding.congr_simp`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding.congr_simp : ∀ (l : ℕ)
  (hl : l ≤ 2),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding_eq : ∀ (l : ℕ)
  (hl : l ≤ 2) (a : Fin l → Bool),
  ↑((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl) a) =
    List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding_lt_pow`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding_lt_pow : ∀ (l : ℕ)
  (hl : l ≤ 2) (a : Fin l → Bool),
  ↑((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl) a) < 2 ^ l
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective : ∀ l ≤ 2,
  Function.Injective fun a => List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective._proof_1_1 : ∀
  (l : ℕ) ⦃a b : Fin l → Bool⦄,
  ((List.ofFn a).getD 0 false).toNat + 2 * ((List.ofFn a).getD 1 false).toNat =
      ((List.ofFn b).getD 0 false).toNat + 2 * ((List.ofFn b).getD 1 false).toNat →
    ((List.ofFn a).getD 0 false).toNat ≤ 1 →
      ((List.ofFn b).getD 0 false).toNat ≤ 1 →
        ¬((List.ofFn a).getD 0 false).toNat = ((List.ofFn b).getD 0 false).toNat → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective._proof_1_2 : ∀
  (l : ℕ) ⦃a b : Fin l → Bool⦄,
  ((List.ofFn a).getD 0 false).toNat + 2 * ((List.ofFn a).getD 1 false).toNat =
      ((List.ofFn b).getD 0 false).toNat + 2 * ((List.ofFn b).getD 1 false).toNat →
    ((List.ofFn a).getD 0 false).toNat = ((List.ofFn b).getD 0 false).toNat →
      ¬((List.ofFn a).getD 1 false).toNat = ((List.ofFn b).getD 1 false).toNat → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective._proof_1_4 : ∀
  l ≤ 2, ∀ ⦃a b : Fin l → Bool⦄ (t : Fin l), ↑t < l → ¬(↑t = 0 ∨ ↑t = 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective._simp_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective._simp_1_3 : ∀
  {b : Bool}, (b.toNat = 1) = (b = true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_four`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_four : ∀ {l : ℕ}
  (a : Fin l → Bool), l ≤ 2 → List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a) < 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_four._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_four._proof_1_1 : ∀
  {l : ℕ} (a : Fin l → Bool),
  ((List.ofFn a).getD 0 false).toNat ≤ 1 →
    ((List.ofFn a).getD 1 false).toNat ≤ 1 →
      ¬((List.ofFn a).getD 0 false).toNat + 2 * ((List.ofFn a).getD 1 false).toNat < 4 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_pow`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_pow : ∀ {l : ℕ}
  (a : Fin l → Bool), l ≤ 2 → List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a) < 2 ^ l
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_pow._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_pow._proof_1_1 : ∀
  {l : ℕ}, l ≤ 2 → ¬(l = 0 ∨ l = 1 ∨ l = 2) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_pow._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_pow._proof_1_2 : ¬0 ≤ 1 →
  False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm : (l : ℕ) →
  l ≤ 2 → (Fin l → Bool) → Equiv.Perm (Fin 4)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm.congr_simp`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm.congr_simp : ∀ (l : ℕ)
  (hl : l ≤ 2) (mask mask_1 : Fin l → Bool),
  mask = mask_1 →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm l hl mask =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm l hl mask_1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_code`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_code : ∀ (l : ℕ)
  (hl : l ≤ 2) (mask a : Fin l → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm l hl mask)
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl) a) =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl)
      ((TCSlib.Cryptography.xorPerm mask) a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_eq : ∀ (l : ℕ) (hl : l ≤ 2)
  (mask : Fin l → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm l hl mask =
    (TCSlib.Cryptography.xorPerm mask).viaFintypeEmbedding
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_unused`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_unused : ∀ (l : ℕ)
  (hl : l ≤ 2) (mask : Fin l → Bool) (a : Fin 4),
  2 ^ l ≤ ↑a → (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm l hl mask) a = a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_unused._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_unused._proof_1_1 : ∀
  (l : ℕ) (hl : l ≤ 2) (a : Fin 4),
  2 ^ l ≤ ↑a →
    ∀ (b : Fin l → Bool),
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl) b = a →
        ↑((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding l hl) b) < 2 ^ l →
          False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask : {m : ℕ} →
  BoolCircuit.DAGCircuit m → (S : ℕ) → (ℕ → Bool) → Fin S → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (w : Fin S),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask C S v w =
    if ↑w < C.size then v ↑w else false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_unused`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_unused : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (w : Fin S),
  C.size ≤ ↑w → TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask C S v w = false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_vertex`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_vertex : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (hS : C.size ≤ S) (w : Fin C.size),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask C S v (Fin.castLE hS w) = v ↑w
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_key_getD`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_key_getD : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool),
  C.size ≤ S →
    ∀ (r : Fin (10 * S * n + 2 * S) → Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
      (List.ofFn
              ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask C S v)
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v)
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v))
                r)).getD
          ((b.toNat * S + ↑w) * n + ↑t) false =
        (List.ofFn r).getD (((b ^^ v ↑w).toNat * S + ↑w) * n + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_row_getD`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_row_getD : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool),
  C.gates.length ≤ S →
    ∀ (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool)
      (t : Fin (2 * n)),
      (List.ofFn
              ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask C S v)
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v)
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v))
                r)).getD
          (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t) false =
        (List.ofFn r).getD
          (2 * S * n +
              (4 * ↑i +
                  List.foldr (fun b k => b.toNat + 2 * k) 0
                    (List.ofFn
                      ((TCSlib.Cryptography.xorPerm
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
                        a))) *
                (2 * n) +
            ↑t)
          false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_shift_getD`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_shift_getD : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool),
  C.gates.length ≤ S →
    ∀ (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin C.gates.length) (t : Fin C.gates[i].args.length),
      (List.ofFn
              ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask C S v)
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v)
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v))
                r)).getD
          (10 * S * n + 2 * ↑i + ↑t) false =
        ((List.ofFn r).getD (10 * S * n + 2 * ↑i + ↑t) false ^^ v C.gates[i].args[t])
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (S : ℕ) → (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) → (ℕ → Bool) → Fin S → Equiv.Perm (Fin 4)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm._proof_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm._proof_3 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (i : Fin S) (hi : ↑i < C.gates.length), ↑⟨↑i, hi⟩ < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm._proof_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm._proof_4 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    ∀ (i : Fin S) (hi : ↑i < C.gates.length), C.gates[⟨↑i, hi⟩].args.length ≤ 2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm.congr_simp`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm.congr_simp : ∀ {m : ℕ}
  (C C_1 : BoolCircuit.DAGCircuit m) (e_C : C = C_1) (S : ℕ)
  (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v v_1 : ℕ → Bool),
  v = v_1 →
    ∀ (i i_1 : Fin S),
      i = i_1 →
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v i =
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C_1 S ⋯ v_1 i_1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool)
  (i : Fin S),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v i =
    if hi : ↑i < C.gates.length then
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm C.gates[↑i].args.length ⋯
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v ⟨↑i, hi⟩)
    else Equiv.refl (Fin 4)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_fold`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_fold : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool)
  (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  ↑((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v (Fin.castLE hG i))
        ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
            C.gates[i].args.length ⋯)
          a)) =
    List.foldr (fun b k => b.toNat + 2 * k) 0
      (List.ofFn
        ((TCSlib.Cryptography.xorPerm
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
          a))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_gate`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_gate : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool)
  (hG : C.gates.length ≤ S) (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v (Fin.castLE hG i) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm C.gates[i].args.length ⋯
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_gate._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_gate._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_unused_code`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_unused_code : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool)
  (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (a : Fin 4),
  2 ^ C.gates[i].args.length ≤ ↑a →
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v (Fin.castLE hG i)) a = a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_unused_gate`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_unused_gate : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool)
  (i : Fin S),
  C.gates.length ≤ ↑i →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v i = Equiv.refl (Fin 4)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool),
  C.size ≤ S →
    ∀
      (seed :
        List Bool →
          TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
      (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
          (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
        (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
            ((seed q).2.1 i a).1 t =
              q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
                false) →
          (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
              ((seed q).2.1 i a).2 t =
                q.getD
                  (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
                  false) →
            (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool)
                (t : Fin C.gates[i].args.length),
                ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
              ∀ (r : Fin (10 * S * n + 2 * S) → Bool),
                seed
                    (List.ofFn
                      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask C S v)
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v)
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v))
                        r)) =
                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v
                    (seed (List.ofFn r))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel._proof_1_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ), m + C.gates.length ≤ S → ¬C.gates.length ≤ S → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel._proof_1_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (t : Fin n), ↑t < n → ¬↑t < 2 * n → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel._proof_1_4 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (t : Fin n), ↑t < n → ¬n + ↑t < 2 * n → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask : {m : ℕ} →
  BoolCircuit.DAGCircuit m → (S : ℕ) → (ℕ → Bool) → Fin S → Fin 2 → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_argument`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_argument : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) (v : ℕ → Bool)
  (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (t : Fin C.gates[i].args.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v (Fin.castLE hG i)
      (Fin.castLE ⋯ t) =
    v C.gates[i].args[t]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_argument._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_argument._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (i : Fin C.gates.length),
  ¬C.gates[i].args.length ≤ C.gates[i].args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (i : Fin S) (t : Fin 2),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v i t =
    if hi : ↑i < C.gates.length then if ht : ↑t < C.gates[↑i].args.length then v C.gates[↑i].args[↑t] else false
    else false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_unused_argument`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_unused_argument : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (t : Fin 2),
  C.gates[i].args.length ≤ ↑t →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v (Fin.castLE hG i) t = false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_unused_gate`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_unused_gate : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (i : Fin S) (t : Fin 2),
  C.gates.length ≤ ↑i → TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v i t = false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.acceptProb_fill`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.acceptProb_fill : ∀ {P : Type u_1}
  {I : Type u_2} {J : Type u_3} {V : Type u_4} [Fintype P] [Fintype I] [Fintype J] [Fintype V] [DecidableEq I]
  [DecidableEq J] {S : Type u_5} {T : Type u_6} {γ : Type u_7} {ρ : Type u_8} [inst : Fintype S] [inst_1 : Fintype T]
  [Nonempty T] [inst_3 : Fintype ρ] (pick : P → I → Option J) (place : P → J → Option I),
  (∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i) →
    ∀ (seedEquiv : S ≃ P × (I → V)) (challengeEquiv : T ≃ (J → V)) (fill : S → T → S),
      (∀ (s : S) (c : T),
          seedEquiv (fill s c) =
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place
                (seedEquiv s, challengeEquiv c)).1) →
        ∀ (X : S → γ) (D : γ → ρ → Bool),
          TCSlib.Cryptography.acceptProb (fun z => X (fill z.1 z.2)) D = TCSlib.Cryptography.acceptProb X D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.acceptProb_swap`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.acceptProb_swap : ∀ {P : Type u_1}
  {I : Type u_2} {J : Type u_3} {V : Type u_4} [inst : Fintype (P × (I → V))] [inst_1 : Fintype (J → V)]
  [Nonempty (J → V)] {γ : Type u_5} {ρ : Type u_6} [inst_3 : Fintype ρ] (pick : P → I → Option J)
  (place : P → J → Option I),
  (∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i) →
    ∀ (X : P × (I → V) → γ) (D : γ → ρ → Bool),
      TCSlib.Cryptography.acceptProb
          (fun s => X (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place s).1) D =
        TCSlib.Cryptography.acceptProb X D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv : {P : Type u_1} →
  {I : Type u_2} →
    {J : Type u_3} →
      {V : Type u_4} →
        (pick : P → I → Option J) →
          (place : P → J → Option I) →
            (∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i) →
              (P × (I → V)) × (J → V) ≃ (P × (I → V)) × (J → V)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv.congr_simp`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv.congr_simp : ∀ {P : Type u_1}
  {I : Type u_2} {J : Type u_3} {V : Type u_4} (pick pick_1 : P → I → Option J) (e_pick : pick = pick_1)
  (place place_1 : P → J → Option I) (e_place : place = place_1)
  (hmatch : ∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv pick place hmatch =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv pick_1 place_1 ⋯
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv_apply`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv_apply : ∀ {P : Type u_1}
  {I : Type u_2} {J : Type u_3} {V : Type u_4} (pick : P → I → Option J) (place : P → J → Option I)
  (hmatch : ∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i) (s : (P × (I → V)) × (J → V)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv pick place hmatch) s =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place s
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv_apply_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv_apply_eq : ∀ {P : Type u_1}
  {I : Type u_2} {J : Type u_3} {V : Type u_4} (pick : P → I → Option J) (place : P → J → Option I)
  (hmatch : ∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i) (s : (P × (I → V)) × (J → V)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv pick place hmatch) s =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place s
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv_symm_apply`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv_symm_apply : ∀ {P : Type u_1}
  {I : Type u_2} {J : Type u_3} {V : Type u_4} (pick : P → I → Option J) (place : P → J → Option I)
  (hmatch : ∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i) (s : (P × (I → V)) × (J → V)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv pick place hmatch).symm s =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place s
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv_symm_apply_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv_symm_apply_eq : ∀ {P : Type u_1}
  {I : Type u_2} {J : Type u_3} {V : Type u_4} (pick : P → I → Option J) (place : P → J → Option I)
  (hmatch : ∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i) (s : (P × (I → V)) × (J → V)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.equiv pick place hmatch).symm s =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place s
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap : {P : Type u_1} →
  {I : Type u_2} →
    {J : Type u_3} →
      {V : Type u_4} → (P → I → Option J) → (P → J → Option I) → (P × (I → V)) × (J → V) → (P × (I → V)) × (J → V)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap_eq : ∀ {P : Type u_1} {I : Type u_2}
  {J : Type u_3} {V : Type u_4} (pick : P → I → Option J) (place : P → J → Option I) (s : (P × (I → V)) × (J → V)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place s =
    ((s.1.1, fun i => (pick s.1.1 i).elim (s.1.2 i) fun j => s.2 j), fun j =>
      (place s.1.1 j).elim (s.2 j) fun i => s.1.2 i)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap_fst`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap_fst : ∀ {P : Type u_1} {I : Type u_2}
  {J : Type u_3} {V : Type u_4} (pick : P → I → Option J) (place : P → J → Option I) (s : (P × (I → V)) × (J → V)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place s).1 =
    (s.1.1, fun i => (pick s.1.1 i).elim (s.1.2 i) fun j => s.2 j)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap_involutive`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap_involutive : ∀ {P : Type u_1}
  {I : Type u_2} {J : Type u_3} {V : Type u_4} (pick : P → I → Option J) (place : P → J → Option I),
  (∀ (p : P) (i : I) (j : J), pick p i = some j ↔ place p j = some i) →
    Function.Involutive (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap_snd`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap_snd : ∀ {P : Type u_1} {I : Type u_2}
  {J : Type u_3} {V : Type u_4} (pick : P → I → Option J) (place : P → J → Option I) (s : (P × (I → V)) × (J → V))
  (j : J),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap.swap pick place s).2 j =
    (place s.1.1 j).elim (s.2 j) fun i => s.1.2 i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription : List Bool →
  List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription_eq : ∀
  (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription w =
    Turing.pairEncode
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit (Complexity.pairFstD w))
      (Complexity.pairSndD w)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription_host`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription_host : ∃ M A c,
  (Turing.ModuleHost.Clean M TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription
      (fun x => []) fun n => A * (n + 1) ^ c) ∧
    (∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
        |(Turing.MultiTapeTM.runFrom (Turing.Cfg.ofWords M.tm.q₀ (Turing.stateWord M.k arg)) v).workTapePos j| ≤
          ↑(A * (arg.length + 1) ^ c)) ∧
      ∀ (n : ℕ) (C : BoolCircuit.DAGCircuit n) (outs : List Bool),
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription
            (Turing.pairEncode C.encode outs) =
          Turing.pairEncode
            (Turing.pairEncode (List.replicate n true)
              (Complexity.BinArith.encWords
                (List.map TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord C.gates)))
            outs
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription_pair`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription_pair : ∀ {n : ℕ}
  (C : BoolCircuit.DAGCircuit n) (outs : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription
      (Turing.pairEncode C.encode outs) =
    Turing.pairEncode
      (Turing.pairEncode (List.replicate n true)
        (Complexity.BinArith.encWords
          (List.map TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord C.gates)))
      outs
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription_poly : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.decodeDescription
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord : BoolCircuit.DAGGate →
  List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord_eq : ∀
  (g : BoolCircuit.DAGGate),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord g =
    Turing.pairEncode g.kind.encode (Complexity.BinArith.encWords (List.map (fun a => List.replicate a true) g.args))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit_encode`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit_encode : ∀ {n : ℕ}
  (C : BoolCircuit.DAGCircuit n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit C.encode =
    Turing.pairEncode (List.replicate n true)
      (Complexity.BinArith.encWords
        (List.map TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord C.gates))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit_eq : ∀ (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit w =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (false, false, false) w
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit_poly : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers : {ρ : Type} →
  {inputs width : ℕ} →
    (C : BoolCircuit.DAGCircuit inputs) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ →
        ℕ → (count : ℕ) → Fin (count * width) → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers_eq : ∀ {ρ : Type}
  {inputs width : ℕ} (C : BoolCircuit.DAGCircuit inputs)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ)
  (t : Fin (count * width)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s first count t =
    TCSlib.Cryptography.SecureComputation.keyAt C s (first + ↑t.divNat) false t.modNat
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair : {K ρ : Type} →
  [Inhabited K] →
    {inputs : ℕ} →
      (C : BoolCircuit.DAGCircuit inputs) → TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ → ℕ → Bool → K × K
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair_eq : ∀ {K ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (v : ℕ) (b : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair C s v b =
    (TCSlib.Cryptography.SecureComputation.keyAt C s v b, TCSlib.Cryptography.SecureComputation.keyAt C s v !b)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message : {inputs width : ℕ} →
  {ρ : Type} →
    TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ →
      (C : BoolCircuit.DAGCircuit inputs) →
        TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ →
          ℕ → (outLen : ℕ) → (Fin outLen → ℕ) → (Fin outLen → Bool) → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message_eq : ∀ {inputs width : ℕ} {ρ : Type}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA outLen : ℕ) (output : Fin outLen → ℕ) (result : Fin outLen → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message M C s inA outLen output result =
    Turing.pairEncode
      (Complexity.BinArith.encWords
        (List.ofFn fun i =>
          Complexity.BinArith.encWords
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table M C s i)))
      (Turing.pairEncode
        (Complexity.BinArith.encWords
          (List.ofFn fun v => List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (↑v) false)))
        (Complexity.BinArith.encWords
          (List.ofFn fun j =>
            Turing.pairEncode
              (List.ofFn
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair C s (output j)
                    (result j)).1)
              (List.ofFn
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair C s (output j)
                    (result j)).2))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row : {K Cipher ρ : Type} →
  [Inhabited K] →
    {inputs : ℕ} →
      TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ →
        (C : BoolCircuit.DAGCircuit inputs) →
          TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ →
            (i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Cipher
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row._proof_1 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row._proof_2 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row_eq : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row M C s i a =
    M.enc (TCSlib.Cryptography.SecureComputation.argKeys C s i a)
      (TCSlib.Cryptography.SecureComputation.keyAt C s (inputs + ↑i) false) (s.2.1 i a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table : {K Cipher ρ : Type} →
  [Inhabited K] →
    {inputs : ℕ} →
      TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ →
        (C : BoolCircuit.DAGCircuit inputs) →
          TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ → Fin C.gates.length → List Cipher
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table_eq : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table M C s i =
    List.map (fun a => TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row M C s i ((s.2.2 i) a))
      Finset.univ.toList
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.activeAnswers_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.activeAnswers_poly : ∀
  (width bound first count inputs : List Bool → ℕ) (coins : List Bool → List Bool),
  (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
    (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (first z) true) →
        (Complexity.PolyTimeComputable fun z => List.replicate (count z) true) →
          Complexity.PolyTimeComputable coins →
            ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
              (s :
                (z : List Bool) →
                  TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                    ((Fin (width z) → Bool) × (Fin (width z) → Bool))),
              (∀ (z : List Bool), first z + count z ≤ inputs z) →
                (∀ (z : List Bool),
                    ∀ v < (C z).size,
                      ∀ (b : Bool),
                        TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                          (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                  Complexity.PolyTimeComputable fun z =>
                    List.ofFn
                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers (C z) (s z)
                        (first z) (count z))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.activeAnswers_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.activeAnswers_poly._proof_1_1 : ∀
  (first count inputs : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z)) (z : List Bool)
  (i : Fin (count z)), first z + count z ≤ inputs z → ¬first z + ↑i < inputs z + (C z).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.activeAnswers_word`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.activeAnswers_word : ∀ {inputs width : ℕ}
  {ρ : Type} (C : BoolCircuit.DAGCircuit inputs)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ),
  List.ofFn (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s first count) =
    (List.ofFn fun i => List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (first + ↑i) false)).flatten
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.inputKeys_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.inputKeys_poly : ∀
  (width bound count inputs : List Bool → ℕ) (coins : List Bool → List Bool),
  (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
    (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (count z) true) →
        Complexity.PolyTimeComputable coins →
          ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
            (s :
              (z : List Bool) →
                TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                  ((Fin (width z) → Bool) × (Fin (width z) → Bool))),
            (∀ (z : List Bool), count z ≤ inputs z) →
              (∀ (z : List Bool),
                  ∀ v < (C z).size,
                    ∀ (b : Bool),
                      TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                        (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                Complexity.PolyTimeComputable fun z =>
                  Complexity.BinArith.encWords
                    (List.ofFn fun v => List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) (↑v) false))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.message_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.message_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ (width bound inputs inA outLen : List Bool → ℕ) (description result coins : List Bool → List Bool),
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              (Complexity.PolyTimeComputable fun z => List.replicate (inA z) true) →
                (Complexity.PolyTimeComputable fun z => List.replicate (outLen z) true) →
                  Complexity.PolyTimeComputable description →
                    Complexity.PolyTimeComputable result →
                      Complexity.PolyTimeComputable coins →
                        ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
                          (s :
                            (z : List Bool) →
                              TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                                ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
                          (output : (z : List Bool) → Fin (outLen z) → ℕ),
                          (∀ (z : List Bool),
                              description z =
                                Turing.pairEncode (C z).encode
                                  (Complexity.BinArith.encWords
                                    (List.ofFn fun j => BoolCircuit.encodeNat (output z j)))) →
                            (∀ (z : List Bool), inA z ≤ inputs z) →
                              (∀ (z : List Bool) (j : Fin (outLen z)), output z j < (C z).size) →
                                (∀ (z : List Bool) (i : Fin (C z).gates.length), (C z).gates[i].args.length ≤ 2) →
                                  (∀ (z : List Bool),
                                      ∀ v < (C z).size,
                                        ∀ (b : Bool),
                                          TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                                            (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                                    (∀ (z : List Bool) (i : Fin (C z).gates.length)
                                        (a : Fin (C z).gates[i].args.length → Bool) (t : Fin (width z)),
                                        ((s z).2.1 i a).1 t =
                                          (coins z).getD
                                            (2 * bound z * width z +
                                                (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                  (2 * width z) +
                                              ↑t)
                                            false) →
                                      (∀ (z : List Bool) (i : Fin (C z).gates.length)
                                          (a : Fin (C z).gates[i].args.length → Bool) (t : Fin (width z)),
                                          ((s z).2.1 i a).2 t =
                                            (coins z).getD
                                              (2 * bound z * width z +
                                                    (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                      (2 * width z) +
                                                  width z +
                                                ↑t)
                                              false) →
                                        (∀ (z : List Bool) (i : Fin (C z).gates.length)
                                            (a : Fin (C z).gates[i].args.length → Bool)
                                            (t : Fin (C z).gates[i].args.length),
                                            ((s z).2.2 i) a t =
                                              (a t ^^ (coins z).getD (10 * bound z * width z + 2 * ↑i + ↑t) false)) →
                                          Complexity.PolyTimeComputable fun z =>
                                            Turing.pairEncode
                                              (Complexity.BinArith.encWords
                                                (List.ofFn fun i =>
                                                  Complexity.BinArith.encWords
                                                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table
                                                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂
                                                        (width z))
                                                      (C z) (s z) i)))
                                              (Turing.pairEncode
                                                (Complexity.BinArith.encWords
                                                  (List.ofFn fun v =>
                                                    List.ofFn
                                                      (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) (↑v)
                                                        false)))
                                                (Complexity.BinArith.encWords
                                                  (List.ofFn fun j =>
                                                    Turing.pairEncode
                                                      (List.ofFn
                                                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair
                                                            (C z) (s z) (output z j) ((result z).getD (↑j) false)).1)
                                                      (List.ofFn
                                                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair
                                                            (C z) (s z) (output z j) ((result z).getD (↑j) false)).2))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.outputPairs_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.outputPairs_poly : ∀
  (width bound count inputs : List Bool → ℕ) (description coins result : List Bool → List Bool),
  (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
    (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (count z) true) →
        Complexity.PolyTimeComputable description →
          Complexity.PolyTimeComputable coins →
            Complexity.PolyTimeComputable result →
              ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
                (s :
                  (z : List Bool) →
                    TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
                (output : (z : List Bool) → Fin (count z) → ℕ),
                (∀ (z : List Bool),
                    Complexity.pairSndD (description z) =
                      Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output z j))) →
                  (∀ (z : List Bool) (j : Fin (count z)), output z j < (C z).size) →
                    (∀ (z : List Bool),
                        ∀ v < (C z).size,
                          ∀ (b : Bool),
                            TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                              (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                      Complexity.PolyTimeComputable fun z =>
                        Complexity.BinArith.encWords
                          (List.ofFn fun j =>
                            Turing.pairEncode
                              (List.ofFn
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair (C z) (s z)
                                    (output z j) ((result z).getD (↑j) false)).1)
                              (List.ofFn
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair (C z) (s z)
                                    (output z j) ((result z).getD (↑j) false)).2))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.swapPairs_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.swapPairs_poly : ∀ (count : List Bool → ℕ)
  (pairs result : List Bool → List Bool) (value : (z : List Bool) → Fin (count z) → List Bool × List Bool),
  (Complexity.PolyTimeComputable fun z => List.replicate (count z) true) →
    Complexity.PolyTimeComputable pairs →
      Complexity.PolyTimeComputable result →
        (∀ (z : List Bool),
            pairs z = Complexity.BinArith.encWords (List.ofFn fun j => Turing.pairEncode (value z j).1 (value z j).2)) →
          Complexity.PolyTimeComputable fun z =>
            Complexity.BinArith.encWords
              (List.ofFn fun j =>
                if (result z).getD (↑j) false = true then Turing.pairEncode (value z j).2 (value z j).1
                else Turing.pairEncode (value z j).1 (value z j).2)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.tables_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.tables_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ (width bound inputs : List Bool → ℕ) (description outs coins : List Bool → List Bool),
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              Complexity.PolyTimeComputable description →
                Complexity.PolyTimeComputable coins →
                  ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
                    (s :
                      (z : List Bool) →
                        TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                          ((Fin (width z) → Bool) × (Fin (width z) → Bool))),
                    (∀ (z : List Bool), description z = Turing.pairEncode (C z).encode (outs z)) →
                      (∀ (z : List Bool) (i : Fin (C z).gates.length), (C z).gates[i].args.length ≤ 2) →
                        (∀ (z : List Bool),
                            ∀ v < (C z).size,
                              ∀ (b : Bool),
                                TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                                  (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                          (∀ (z : List Bool) (i : Fin (C z).gates.length) (a : Fin (C z).gates[i].args.length → Bool)
                              (t : Fin (width z)),
                              ((s z).2.1 i a).1 t =
                                (coins z).getD
                                  (2 * bound z * width z +
                                      (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                        (2 * width z) +
                                    ↑t)
                                  false) →
                            (∀ (z : List Bool) (i : Fin (C z).gates.length) (a : Fin (C z).gates[i].args.length → Bool)
                                (t : Fin (width z)),
                                ((s z).2.1 i a).2 t =
                                  (coins z).getD
                                    (2 * bound z * width z +
                                          (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                            (2 * width z) +
                                        width z +
                                      ↑t)
                                    false) →
                              (∀ (z : List Bool) (i : Fin (C z).gates.length)
                                  (a : Fin (C z).gates[i].args.length → Bool) (t : Fin (C z).gates[i].args.length),
                                  ((s z).2.2 i) a t =
                                    (a t ^^ (coins z).getD (10 * bound z * width z + 2 * ↑i + ↑t) false)) →
                                Complexity.PolyTimeComputable fun z =>
                                  Complexity.BinArith.encWords
                                    (List.ofFn fun i =>
                                      Complexity.BinArith.encWords
                                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table
                                          (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)) (C z)
                                          (s z) i))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.tables_poly._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.tables_poly._proof_1 : ∀
  (inputs : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z)) (z : List Bool),
  ¬(C z).gates.length ≤ (C z).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.tables_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram.tables_poly._proof_1_1 : ∀
  (inputs : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z)) (z : List Bool)
  (i : Fin (C z).gates.length), ¬↑i < (C z).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data : Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.E₁`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.E₁ : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.E₁_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.E₁_poly : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data),
  Complexity.PolyTimeComputable self.E₁
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.E₂`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.E₂ : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.E₂_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.E₂_poly : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data),
  Complexity.PolyTimeComputable self.E₂
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data._proof_1 : ∀
  (inputs : Complexity.PolyExpr) (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (n : ℕ),
  ¬(circuit n).gates.length ≤ (circuit n).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data._sizeOf_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data._sizeOf_1 : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data._sizeOf_inst`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data._sizeOf_inst : SizeOf
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.bound`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.bound : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.casesOn`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.casesOn : {motive :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data → Sort u} →
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) →
    ((E₁ E₂ : List Bool → List Bool) →
        (E₁_poly : Complexity.PolyTimeComputable E₁) →
          (E₂_poly : Complexity.PolyTimeComputable E₂) →
            (bound inputs inA inB outLen : Complexity.PolyExpr) →
              (gen : List Bool → List Bool) →
                (gen_poly : Complexity.PolyTimeComputable gen) →
                  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) →
                    (output : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
                      (shape :
                          ∀ (n : ℕ),
                            gen (List.replicate n true) =
                              Turing.pairEncode (circuit n).encode
                                (Complexity.BinArith.encWords
                                  (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
                        (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                          (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                            (fanin :
                                ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                              (seed :
                                  (n : ℕ) →
                                    List Bool →
                                      TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                                        ((Fin n → Bool) × (Fin n → Bool))) →
                                (key :
                                    ∀ (n : ℕ) (r : List Bool),
                                      ∀ v < (circuit n).size,
                                        ∀ (b : Bool),
                                          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b =
                                            fun t => r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                                  (nonce₀ :
                                      ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                        (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                        ((seed n r).2.1 i a).1 t =
                                          r.getD
                                            (2 * bound.eval n * n +
                                                (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                  (2 * n) +
                                              ↑t)
                                            false) →
                                    (nonce₁ :
                                        ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                          (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                          ((seed n r).2.1 i a).2 t =
                                            r.getD
                                              (2 * bound.eval n * n +
                                                    (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                      (2 * n) +
                                                  n +
                                                ↑t)
                                              false) →
                                      (permutation :
                                          ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                            (a : Fin (circuit n).gates[i].args.length → Bool)
                                            (t : Fin (circuit n).gates[i].args.length),
                                            ((seed n r).2.2 i) a t =
                                              (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                                        motive
                                          { E₁ := E₁, E₂ := E₂, E₁_poly := E₁_poly, E₂_poly := E₂_poly, bound := bound,
                                            inputs := inputs, inA := inA, inB := inB, outLen := outLen, gen := gen,
                                            gen_poly := gen_poly, circuit := circuit, output := output, shape := shape,
                                            input_range := input_range, output_lt := output_lt, fanin := fanin,
                                            seed := seed, key := key, nonce₀ := nonce₀, nonce₁ := nonce₁,
                                            permutation := permutation }) →
      motive t
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.circuit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.circuit : (self :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) →
  (n : ℕ) → BoolCircuit.DAGCircuit (self.inputs.eval n)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.ctorIdx`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.ctorIdx : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.fanin`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.fanin : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ)
  (i : Fin (self.circuit n).gates.length), (self.circuit n).gates[i].args.length ≤ 2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.gen`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.gen : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.gen_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.gen_poly : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data),
  Complexity.PolyTimeComputable self.gen
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.inA`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.inA : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.inB`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.inB : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.input_range`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.input_range : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ),
  self.inA.eval n + self.inB.eval n ≤ self.inputs.eval n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.inputs`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.inputs : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.key : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (r : List Bool),
  ∀ v < (self.circuit n).size,
    ∀ (b : Bool),
      TCSlib.Cryptography.SecureComputation.keyAt (self.circuit n) (self.seed n r) v b = fun t =>
        r.getD ((b.toNat * self.bound.eval n + v) * n + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make : (E₁ E₂ : List Bool → List Bool) →
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      (bound inputs inA inB outLen : Complexity.PolyExpr) →
        (gen : List Bool → List Bool) →
          Complexity.PolyTimeComputable gen →
            (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) →
              (output : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
                (∀ (n : ℕ),
                    gen (List.replicate n true) =
                      Turing.pairEncode (circuit n).encode
                        (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
                  (∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                    (∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                      (∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                        (seed :
                            (n : ℕ) →
                              List Bool →
                                TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                                  ((Fin n → Bool) × (Fin n → Bool))) →
                          (∀ (n : ℕ) (r : List Bool),
                              ∀ v < (circuit n).size,
                                ∀ (b : Bool),
                                  TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
                                    r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                            (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                ((seed n r).2.1 i a).1 t =
                                  r.getD
                                    (2 * bound.eval n * n +
                                        (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                      ↑t)
                                    false) →
                              (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                  (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                  ((seed n r).2.1 i a).2 t =
                                    r.getD
                                      (2 * bound.eval n * n +
                                            (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                              (2 * n) +
                                          n +
                                        ↑t)
                                      false) →
                                (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                    (a : Fin (circuit n).gates[i].args.length → Bool)
                                    (t : Fin (circuit n).gates[i].args.length),
                                    ((seed n r).2.2 i) a t =
                                      (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make._proof_1 : ∀
  (inputs : Complexity.PolyExpr) (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (n : ℕ)
  (i : Fin (circuit n).gates.length), ↑i < (circuit n).gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_E₁`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_E₁ : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (a : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
          inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
          permutation).E₁
      a =
    E₁ a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_E₂`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_E₂ : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (a : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
          inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
          permutation).E₂
      a =
    E₂ a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_answersAt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_answersAt : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (n : ℕ) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs
        inA inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁ permutation)
      n r =
    List.ofFn
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers (circuit n) (seed n r)
        (inA.eval n) (inB.eval n))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_bound`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_bound : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
        inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
        permutation).bound =
    bound
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_circuit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_circuit : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (n : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
          inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
          permutation).circuit
      n =
    circuit n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_gen`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_gen : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (a : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
          inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
          permutation).gen
      a =
    gen a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_inA`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_inA : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
        inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
        permutation).inA =
    inA
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_inB`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_inB : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
        inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
        permutation).inB =
    inB
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_inputs`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_inputs : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
        inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
        permutation).inputs =
    inputs
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_messageAt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_messageAt : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (n : ℕ) (r f : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs
        inA inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁ permutation)
      n r f =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message
      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (circuit n) (seed n r) (inA.eval n) (outLen.eval n)
      (output n) fun j => f.getD (↑j) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_outLen`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_outLen : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
        inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
        permutation).outLen =
    outLen
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_output`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_output : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (n : ℕ) (a : Fin (outLen.eval n)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
          inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
          permutation).output
      n a =
    output n a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_seed`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make_seed : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (n : ℕ) (a : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.make E₁ E₂ E₁_poly E₂_poly bound inputs inA
          inB outLen gen gen_poly circuit output shape input_range output_lt fanin seed key nonce₀ nonce₁
          permutation).seed
      n a =
    seed n a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk : (E₁ E₂ : List Bool → List Bool) →
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      (bound inputs inA inB outLen : Complexity.PolyExpr) →
        (gen : List Bool → List Bool) →
          Complexity.PolyTimeComputable gen →
            (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) →
              (output : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
                (∀ (n : ℕ),
                    gen (List.replicate n true) =
                      Turing.pairEncode (circuit n).encode
                        (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
                  (∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                    (∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                      (∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                        (seed :
                            (n : ℕ) →
                              List Bool →
                                TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                                  ((Fin n → Bool) × (Fin n → Bool))) →
                          (∀ (n : ℕ) (r : List Bool),
                              ∀ v < (circuit n).size,
                                ∀ (b : Bool),
                                  TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
                                    r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                            (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                ((seed n r).2.1 i a).1 t =
                                  r.getD
                                    (2 * bound.eval n * n +
                                        (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                      ↑t)
                                    false) →
                              (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                  (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                  ((seed n r).2.1 i a).2 t =
                                    r.getD
                                      (2 * bound.eval n * n +
                                            (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                              (2 * n) +
                                          n +
                                        ↑t)
                                      false) →
                                (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                    (a : Fin (circuit n).gates[i].args.length → Bool)
                                    (t : Fin (circuit n).gates[i].args.length),
                                    ((seed n r).2.2 i) a t =
                                      (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk._flat_ctor`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk._flat_ctor : (E₁ E₂ :
    List Bool → List Bool) →
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      (bound inputs inA inB outLen : Complexity.PolyExpr) →
        (gen : List Bool → List Bool) →
          Complexity.PolyTimeComputable gen →
            (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) →
              (output : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
                (∀ (n : ℕ),
                    gen (List.replicate n true) =
                      Turing.pairEncode (circuit n).encode
                        (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
                  (∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                    (∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                      (∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                        (seed :
                            (n : ℕ) →
                              List Bool →
                                TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                                  ((Fin n → Bool) × (Fin n → Bool))) →
                          (∀ (n : ℕ) (r : List Bool),
                              ∀ v < (circuit n).size,
                                ∀ (b : Bool),
                                  TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
                                    r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                            (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                ((seed n r).2.1 i a).1 t =
                                  r.getD
                                    (2 * bound.eval n * n +
                                        (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                      ↑t)
                                    false) →
                              (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                  (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                  ((seed n r).2.1 i a).2 t =
                                    r.getD
                                      (2 * bound.eval n * n +
                                            (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                              (2 * n) +
                                          n +
                                        ↑t)
                                      false) →
                                (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                    (a : Fin (circuit n).gates[i].args.length → Bool)
                                    (t : Fin (circuit n).gates[i].args.length),
                                    ((seed n r).2.2 i) a t =
                                      (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk.inj`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk.inj : ∀
  {E₁ E₂ : List Bool → List Bool} {E₁_poly : Complexity.PolyTimeComputable E₁}
  {E₂_poly : Complexity.PolyTimeComputable E₂} {bound inputs inA inB outLen : Complexity.PolyExpr}
  {gen : List Bool → List Bool} {gen_poly : Complexity.PolyTimeComputable gen}
  {circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)} {output : (n : ℕ) → Fin (outLen.eval n) → ℕ}
  {shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))}
  {input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n}
  {output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size}
  {fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2}
  {seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))}
  {key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false}
  {nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false}
  {nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false}
  {permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)}
  {E₁_1 E₂_1 : List Bool → List Bool} {E₁_poly_1 : Complexity.PolyTimeComputable E₁_1}
  {E₂_poly_1 : Complexity.PolyTimeComputable E₂_1} {bound_1 inputs_1 inA_1 inB_1 outLen_1 : Complexity.PolyExpr}
  {gen_1 : List Bool → List Bool} {gen_poly_1 : Complexity.PolyTimeComputable gen_1}
  {circuit_1 : (n : ℕ) → BoolCircuit.DAGCircuit (inputs_1.eval n)} {output_1 : (n : ℕ) → Fin (outLen_1.eval n) → ℕ}
  {shape_1 :
    ∀ (n : ℕ),
      gen_1 (List.replicate n true) =
        Turing.pairEncode (circuit_1 n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output_1 n j)))}
  {input_range_1 : ∀ (n : ℕ), inA_1.eval n + inB_1.eval n ≤ inputs_1.eval n}
  {output_lt_1 : ∀ (n : ℕ) (j : Fin (outLen_1.eval n)), output_1 n j < (circuit_1 n).size}
  {fanin_1 : ∀ (n : ℕ) (i : Fin (circuit_1 n).gates.length), (circuit_1 n).gates[i].args.length ≤ 2}
  {seed_1 :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit_1 n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))}
  {key_1 :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit_1 n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit_1 n) (seed_1 n r) v b = fun t =>
            r.getD ((b.toNat * bound_1.eval n + v) * n + ↑t) false}
  {nonce₀_1 :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit_1 n).gates.length) (a : Fin (circuit_1 n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed_1 n r).2.1 i a).1 t =
        r.getD
          (2 * bound_1.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false}
  {nonce₁_1 :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit_1 n).gates.length) (a : Fin (circuit_1 n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed_1 n r).2.1 i a).2 t =
        r.getD
          (2 * bound_1.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n +
            ↑t)
          false}
  {permutation_1 :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit_1 n).gates.length) (a : Fin (circuit_1 n).gates[i].args.length → Bool)
      (t : Fin (circuit_1 n).gates[i].args.length),
      ((seed_1 n r).2.2 i) a t = (a t ^^ r.getD (10 * bound_1.eval n * n + 2 * ↑i + ↑t) false)},
  { E₁ := E₁, E₂ := E₂, E₁_poly := E₁_poly, E₂_poly := E₂_poly, bound := bound, inputs := inputs, inA := inA,
        inB := inB, outLen := outLen, gen := gen, gen_poly := gen_poly, circuit := circuit, output := output,
        shape := shape, input_range := input_range, output_lt := output_lt, fanin := fanin, seed := seed, key := key,
        nonce₀ := nonce₀, nonce₁ := nonce₁, permutation := permutation } =
      { E₁ := E₁_1, E₂ := E₂_1, E₁_poly := E₁_poly_1, E₂_poly := E₂_poly_1, bound := bound_1, inputs := inputs_1,
        inA := inA_1, inB := inB_1, outLen := outLen_1, gen := gen_1, gen_poly := gen_poly_1, circuit := circuit_1,
        output := output_1, shape := shape_1, input_range := input_range_1, output_lt := output_lt_1, fanin := fanin_1,
        seed := seed_1, key := key_1, nonce₀ := nonce₀_1, nonce₁ := nonce₁_1, permutation := permutation_1 } →
    E₁ = E₁_1 ∧
      E₂ = E₂_1 ∧
        bound = bound_1 ∧
          inputs = inputs_1 ∧
            inA = inA_1 ∧
              inB = inB_1 ∧ outLen = outLen_1 ∧ gen = gen_1 ∧ circuit ≍ circuit_1 ∧ output ≍ output_1 ∧ seed ≍ seed_1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk.injEq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk.injEq : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false))
  (E₁_1 E₂_1 : List Bool → List Bool) (E₁_poly_1 : Complexity.PolyTimeComputable E₁_1)
  (E₂_poly_1 : Complexity.PolyTimeComputable E₂_1) (bound_1 inputs_1 inA_1 inB_1 outLen_1 : Complexity.PolyExpr)
  (gen_1 : List Bool → List Bool) (gen_poly_1 : Complexity.PolyTimeComputable gen_1)
  (circuit_1 : (n : ℕ) → BoolCircuit.DAGCircuit (inputs_1.eval n)) (output_1 : (n : ℕ) → Fin (outLen_1.eval n) → ℕ)
  (shape_1 :
    ∀ (n : ℕ),
      gen_1 (List.replicate n true) =
        Turing.pairEncode (circuit_1 n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output_1 n j))))
  (input_range_1 : ∀ (n : ℕ), inA_1.eval n + inB_1.eval n ≤ inputs_1.eval n)
  (output_lt_1 : ∀ (n : ℕ) (j : Fin (outLen_1.eval n)), output_1 n j < (circuit_1 n).size)
  (fanin_1 : ∀ (n : ℕ) (i : Fin (circuit_1 n).gates.length), (circuit_1 n).gates[i].args.length ≤ 2)
  (seed_1 :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit_1 n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key_1 :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit_1 n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit_1 n) (seed_1 n r) v b = fun t =>
            r.getD ((b.toNat * bound_1.eval n + v) * n + ↑t) false)
  (nonce₀_1 :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit_1 n).gates.length) (a : Fin (circuit_1 n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed_1 n r).2.1 i a).1 t =
        r.getD
          (2 * bound_1.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁_1 :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit_1 n).gates.length) (a : Fin (circuit_1 n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed_1 n r).2.1 i a).2 t =
        r.getD
          (2 * bound_1.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n +
            ↑t)
          false)
  (permutation_1 :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit_1 n).gates.length) (a : Fin (circuit_1 n).gates[i].args.length → Bool)
      (t : Fin (circuit_1 n).gates[i].args.length),
      ((seed_1 n r).2.2 i) a t = (a t ^^ r.getD (10 * bound_1.eval n * n + 2 * ↑i + ↑t) false)),
  ({ E₁ := E₁, E₂ := E₂, E₁_poly := E₁_poly, E₂_poly := E₂_poly, bound := bound, inputs := inputs, inA := inA,
        inB := inB, outLen := outLen, gen := gen, gen_poly := gen_poly, circuit := circuit, output := output,
        shape := shape, input_range := input_range, output_lt := output_lt, fanin := fanin, seed := seed, key := key,
        nonce₀ := nonce₀, nonce₁ := nonce₁, permutation := permutation } =
      { E₁ := E₁_1, E₂ := E₂_1, E₁_poly := E₁_poly_1, E₂_poly := E₂_poly_1, bound := bound_1, inputs := inputs_1,
        inA := inA_1, inB := inB_1, outLen := outLen_1, gen := gen_1, gen_poly := gen_poly_1, circuit := circuit_1,
        output := output_1, shape := shape_1, input_range := input_range_1, output_lt := output_lt_1, fanin := fanin_1,
        seed := seed_1, key := key_1, nonce₀ := nonce₀_1, nonce₁ := nonce₁_1, permutation := permutation_1 }) =
    (E₁ = E₁_1 ∧
      E₂ = E₂_1 ∧
        bound = bound_1 ∧
          inputs = inputs_1 ∧
            inA = inA_1 ∧
              inB = inB_1 ∧ outLen = outLen_1 ∧ gen = gen_1 ∧ circuit ≍ circuit_1 ∧ output ≍ output_1 ∧ seed ≍ seed_1)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk.noConfusion`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk.noConfusion : (P : Sort u) →
  (E₁ E₂ : List Bool → List Bool) →
    (E₁_poly : Complexity.PolyTimeComputable E₁) →
      (E₂_poly : Complexity.PolyTimeComputable E₂) →
        (bound inputs inA inB outLen : Complexity.PolyExpr) →
          (gen : List Bool → List Bool) →
            (gen_poly : Complexity.PolyTimeComputable gen) →
              (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) →
                (output : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
                  (shape :
                      ∀ (n : ℕ),
                        gen (List.replicate n true) =
                          Turing.pairEncode (circuit n).encode
                            (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
                    (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                      (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                        (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                          (seed :
                              (n : ℕ) →
                                List Bool →
                                  TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                                    ((Fin n → Bool) × (Fin n → Bool))) →
                            (key :
                                ∀ (n : ℕ) (r : List Bool),
                                  ∀ v < (circuit n).size,
                                    ∀ (b : Bool),
                                      TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
                                        r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                              (nonce₀ :
                                  ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                    (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                    ((seed n r).2.1 i a).1 t =
                                      r.getD
                                        (2 * bound.eval n * n +
                                            (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                              (2 * n) +
                                          ↑t)
                                        false) →
                                (nonce₁ :
                                    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                      (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                      ((seed n r).2.1 i a).2 t =
                                        r.getD
                                          (2 * bound.eval n * n +
                                                (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                  (2 * n) +
                                              n +
                                            ↑t)
                                          false) →
                                  (permutation :
                                      ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                        (a : Fin (circuit n).gates[i].args.length → Bool)
                                        (t : Fin (circuit n).gates[i].args.length),
                                        ((seed n r).2.2 i) a t =
                                          (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                                    (E₁' E₂' : List Bool → List Bool) →
                                      (E₁_poly' : Complexity.PolyTimeComputable E₁') →
                                        (E₂_poly' : Complexity.PolyTimeComputable E₂') →
                                          (bound' inputs' inA' inB' outLen' : Complexity.PolyExpr) →
                                            (gen' : List Bool → List Bool) →
                                              (gen_poly' : Complexity.PolyTimeComputable gen') →
                                                (circuit' : (n : ℕ) → BoolCircuit.DAGCircuit (inputs'.eval n)) →
                                                  (output' : (n : ℕ) → Fin (outLen'.eval n) → ℕ) →
                                                    (shape' :
                                                        ∀ (n : ℕ),
                                                          gen' (List.replicate n true) =
                                                            Turing.pairEncode (circuit' n).encode
                                                              (Complexity.BinArith.encWords
                                                                (List.ofFn fun j =>
                                                                  BoolCircuit.encodeNat (output' n j)))) →
                                                      (input_range' :
                                                          ∀ (n : ℕ), inA'.eval n + inB'.eval n ≤ inputs'.eval n) →
                                                        (output_lt' :
                                                            ∀ (n : ℕ) (j : Fin (outLen'.eval n)),
                                                              output' n j < (circuit' n).size) →
                                                          (fanin' :
                                                              ∀ (n : ℕ) (i : Fin (circuit' n).gates.length),
                                                                (circuit' n).gates[i].args.length ≤ 2) →
                                                            (seed' :
                                                                (n : ℕ) →
                                                                  List Bool →
                                                                    TCSlib.Cryptography.SecureComputation.GarbleSeed
                                                                      (circuit' n) (Fin n → Bool)
                                                                      ((Fin n → Bool) × (Fin n → Bool))) →
                                                              (key' :
                                                                  ∀ (n : ℕ) (r : List Bool),
                                                                    ∀ v < (circuit' n).size,
                                                                      ∀ (b : Bool),
                                                                        TCSlib.Cryptography.SecureComputation.keyAt
                                                                            (circuit' n) (seed' n r) v b =
                                                                          fun t =>
                                                                          r.getD
                                                                            ((b.toNat * bound'.eval n + v) * n + ↑t)
                                                                            false) →
                                                                (nonce₀' :
                                                                    ∀ (n : ℕ) (r : List Bool)
                                                                      (i : Fin (circuit' n).gates.length)
                                                                      (a : Fin (circuit' n).gates[i].args.length → Bool)
                                                                      (t : Fin n),
                                                                      ((seed' n r).2.1 i a).1 t =
                                                                        r.getD
                                                                          (2 * bound'.eval n * n +
                                                                              (4 * ↑i +
                                                                                  List.foldr
                                                                                    (fun b k => b.toNat + 2 * k) 0
                                                                                    (List.ofFn a)) *
                                                                                (2 * n) +
                                                                            ↑t)
                                                                          false) →
                                                                  (nonce₁' :
                                                                      ∀ (n : ℕ) (r : List Bool)
                                                                        (i : Fin (circuit' n).gates.length)
                                                                        (a :
                                                                          Fin (circuit' n).gates[i].args.length → Bool)
                                                                        (t : Fin n),
                                                                        ((seed' n r).2.1 i a).2 t =
                                                                          r.getD
                                                                            (2 * bound'.eval n * n +
                                                                                  (4 * ↑i +
                                                                                      List.foldr
                                                                                        (fun b k => b.toNat + 2 * k) 0
                                                                                        (List.ofFn a)) *
                                                                                    (2 * n) +
                                                                                n +
                                                                              ↑t)
                                                                            false) →
                                                                    (permutation' :
                                                                        ∀ (n : ℕ) (r : List Bool)
                                                                          (i : Fin (circuit' n).gates.length)
                                                                          (a :
                                                                            Fin (circuit' n).gates[i].args.length →
                                                                              Bool)
                                                                          (t : Fin (circuit' n).gates[i].args.length),
                                                                          ((seed' n r).2.2 i) a t =
                                                                            (a t ^^
                                                                              r.getD
                                                                                (10 * bound'.eval n * n + 2 * ↑i + ↑t)
                                                                                false)) →
                                                                      { E₁ := E₁, E₂ := E₂, E₁_poly := E₁_poly,
                                                                            E₂_poly := E₂_poly, bound := bound,
                                                                            inputs := inputs, inA := inA, inB := inB,
                                                                            outLen := outLen, gen := gen,
                                                                            gen_poly := gen_poly, circuit := circuit,
                                                                            output := output, shape := shape,
                                                                            input_range := input_range,
                                                                            output_lt := output_lt, fanin := fanin,
                                                                            seed := seed, key := key, nonce₀ := nonce₀,
                                                                            nonce₁ := nonce₁,
                                                                            permutation := permutation } =
                                                                          { E₁ := E₁', E₂ := E₂', E₁_poly := E₁_poly',
                                                                            E₂_poly := E₂_poly', bound := bound',
                                                                            inputs := inputs', inA := inA', inB := inB',
                                                                            outLen := outLen', gen := gen',
                                                                            gen_poly := gen_poly', circuit := circuit',
                                                                            output := output', shape := shape',
                                                                            input_range := input_range',
                                                                            output_lt := output_lt', fanin := fanin',
                                                                            seed := seed', key := key',
                                                                            nonce₀ := nonce₀', nonce₁ := nonce₁',
                                                                            permutation := permutation' } →
                                                                        (E₁ = E₁' →
                                                                            E₂ = E₂' →
                                                                              bound = bound' →
                                                                                inputs = inputs' →
                                                                                  inA = inA' →
                                                                                    inB = inB' →
                                                                                      outLen = outLen' →
                                                                                        gen = gen' →
                                                                                          circuit ≍ circuit' →
                                                                                            output ≍ output' →
                                                                                              seed ≍ seed' → P) →
                                                                          P
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk.sizeOf_spec`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.mk.sizeOf_spec : ∀
  (E₁ E₂ : List Bool → List Bool) (E₁_poly : Complexity.PolyTimeComputable E₁)
  (E₂_poly : Complexity.PolyTimeComputable E₂) (bound inputs inA inB outLen : Complexity.PolyExpr)
  (gen : List Bool → List Bool) (gen_poly : Complexity.PolyTimeComputable gen)
  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ)
  (shape :
    ∀ (n : ℕ),
      gen (List.replicate n true) =
        Turing.pairEncode (circuit n).encode
          (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j))))
  (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n)
  (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size)
  (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (key :
    ∀ (n : ℕ) (r : List Bool),
      ∀ v < (circuit n).size,
        ∀ (b : Bool),
          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
            r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false)
  (nonce₀ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).1 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
          false)
  (nonce₁ :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin n),
      ((seed n r).2.1 i a).2 t =
        r.getD
          (2 * bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
          false)
  (permutation :
    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length) (a : Fin (circuit n).gates[i].args.length → Bool)
      (t : Fin (circuit n).gates[i].args.length),
      ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)),
  sizeOf
      { E₁ := E₁, E₂ := E₂, E₁_poly := E₁_poly, E₂_poly := E₂_poly, bound := bound, inputs := inputs, inA := inA,
        inB := inB, outLen := outLen, gen := gen, gen_poly := gen_poly, circuit := circuit, output := output,
        shape := shape, input_range := input_range, output_lt := output_lt, fanin := fanin, seed := seed, key := key,
        nonce₀ := nonce₀, nonce₁ := nonce₁, permutation := permutation } =
    1 + sizeOf E₁_poly + sizeOf E₂_poly + sizeOf bound + sizeOf inputs + sizeOf inA + sizeOf inB + sizeOf outLen +
      sizeOf gen_poly
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.noConfusion`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.noConfusion : {P : Sort u} →
  {x1 x2 : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data} →
    x1 = x2 → TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.noConfusionType P x1 x2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.noConfusionType`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.noConfusionType : Sort u →
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data → Sort u
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.nonce₀`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.nonce₀ : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (r : List Bool)
  (i : Fin (self.circuit n).gates.length) (a : Fin (self.circuit n).gates[i].args.length → Bool) (t : Fin n),
  ((self.seed n r).2.1 i a).1 t =
    r.getD
      (2 * self.bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
      false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.nonce₁`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.nonce₁ : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (r : List Bool)
  (i : Fin (self.circuit n).gates.length) (a : Fin (self.circuit n).gates[i].args.length → Bool) (t : Fin n),
  ((self.seed n r).2.1 i a).2 t =
    r.getD
      (2 * self.bound.eval n * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n +
        ↑t)
      false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.outLen`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.outLen : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.output`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.output : (self :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) →
  (n : ℕ) → Fin (self.outLen.eval n) → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.output_lt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.output_lt : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ)
  (j : Fin (self.outLen.eval n)), self.output n j < (self.circuit n).size
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.permutation`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.permutation : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (r : List Bool)
  (i : Fin (self.circuit n).gates.length) (a : Fin (self.circuit n).gates[i].args.length → Bool)
  (t : Fin (self.circuit n).gates[i].args.length),
  ((self.seed n r).2.2 i) a t = (a t ^^ r.getD (10 * self.bound.eval n * n + 2 * ↑i + ↑t) false)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.rec`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.rec : {motive :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data → Sort u} →
  ((E₁ E₂ : List Bool → List Bool) →
      (E₁_poly : Complexity.PolyTimeComputable E₁) →
        (E₂_poly : Complexity.PolyTimeComputable E₂) →
          (bound inputs inA inB outLen : Complexity.PolyExpr) →
            (gen : List Bool → List Bool) →
              (gen_poly : Complexity.PolyTimeComputable gen) →
                (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) →
                  (output : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
                    (shape :
                        ∀ (n : ℕ),
                          gen (List.replicate n true) =
                            Turing.pairEncode (circuit n).encode
                              (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
                      (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                        (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                          (fanin : ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                            (seed :
                                (n : ℕ) →
                                  List Bool →
                                    TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                                      ((Fin n → Bool) × (Fin n → Bool))) →
                              (key :
                                  ∀ (n : ℕ) (r : List Bool),
                                    ∀ v < (circuit n).size,
                                      ∀ (b : Bool),
                                        TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b =
                                          fun t => r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                                (nonce₀ :
                                    ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                      (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                      ((seed n r).2.1 i a).1 t =
                                        r.getD
                                          (2 * bound.eval n * n +
                                              (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                (2 * n) +
                                            ↑t)
                                          false) →
                                  (nonce₁ :
                                      ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                        (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                        ((seed n r).2.1 i a).2 t =
                                          r.getD
                                            (2 * bound.eval n * n +
                                                  (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                    (2 * n) +
                                                n +
                                              ↑t)
                                            false) →
                                    (permutation :
                                        ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                          (a : Fin (circuit n).gates[i].args.length → Bool)
                                          (t : Fin (circuit n).gates[i].args.length),
                                          ((seed n r).2.2 i) a t =
                                            (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                                      motive
                                        { E₁ := E₁, E₂ := E₂, E₁_poly := E₁_poly, E₂_poly := E₂_poly, bound := bound,
                                          inputs := inputs, inA := inA, inB := inB, outLen := outLen, gen := gen,
                                          gen_poly := gen_poly, circuit := circuit, output := output, shape := shape,
                                          input_range := input_range, output_lt := output_lt, fanin := fanin,
                                          seed := seed, key := key, nonce₀ := nonce₀, nonce₁ := nonce₁,
                                          permutation := permutation }) →
    (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) → motive t
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.recOn`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.recOn : {motive :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data → Sort u} →
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) →
    ((E₁ E₂ : List Bool → List Bool) →
        (E₁_poly : Complexity.PolyTimeComputable E₁) →
          (E₂_poly : Complexity.PolyTimeComputable E₂) →
            (bound inputs inA inB outLen : Complexity.PolyExpr) →
              (gen : List Bool → List Bool) →
                (gen_poly : Complexity.PolyTimeComputable gen) →
                  (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) →
                    (output : (n : ℕ) → Fin (outLen.eval n) → ℕ) →
                      (shape :
                          ∀ (n : ℕ),
                            gen (List.replicate n true) =
                              Turing.pairEncode (circuit n).encode
                                (Complexity.BinArith.encWords
                                  (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
                        (input_range : ∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                          (output_lt : ∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                            (fanin :
                                ∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                              (seed :
                                  (n : ℕ) →
                                    List Bool →
                                      TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                                        ((Fin n → Bool) × (Fin n → Bool))) →
                                (key :
                                    ∀ (n : ℕ) (r : List Bool),
                                      ∀ v < (circuit n).size,
                                        ∀ (b : Bool),
                                          TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b =
                                            fun t => r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                                  (nonce₀ :
                                      ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                        (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                        ((seed n r).2.1 i a).1 t =
                                          r.getD
                                            (2 * bound.eval n * n +
                                                (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                  (2 * n) +
                                              ↑t)
                                            false) →
                                    (nonce₁ :
                                        ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                          (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                                          ((seed n r).2.1 i a).2 t =
                                            r.getD
                                              (2 * bound.eval n * n +
                                                    (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                      (2 * n) +
                                                  n +
                                                ↑t)
                                              false) →
                                      (permutation :
                                          ∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                            (a : Fin (circuit n).gates[i].args.length → Bool)
                                            (t : Fin (circuit n).gates[i].args.length),
                                            ((seed n r).2.2 i) a t =
                                              (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                                        motive
                                          { E₁ := E₁, E₂ := E₂, E₁_poly := E₁_poly, E₂_poly := E₂_poly, bound := bound,
                                            inputs := inputs, inA := inA, inB := inB, outLen := outLen, gen := gen,
                                            gen_poly := gen_poly, circuit := circuit, output := output, shape := shape,
                                            input_range := input_range, output_lt := output_lt, fanin := fanin,
                                            seed := seed, key := key, nonce₀ := nonce₀, nonce₁ := nonce₁,
                                            permutation := permutation }) →
      motive t
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.seed`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.seed : (self :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) →
  (n : ℕ) →
    List Bool →
      TCSlib.Cryptography.SecureComputation.GarbleSeed (self.circuit n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.shape`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data.shape : ∀
  (self : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ),
  self.gen (List.replicate n true) =
    Turing.pairEncode (self.circuit n).encode
      (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (self.output n j)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  ℕ → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt_eq : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt d n r =
    List.ofFn
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers (d.circuit n) (d.seed n r)
        (d.inA.eval n) (d.inB.eval n))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers_eq : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers d z =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt d
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) (Complexity.NUPPT.inCoins z)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers_layout : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (arg advice r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers d
      (Complexity.NUPPT.layout (List.replicate n true) arg advice r) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt d n r
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers_poly : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data),
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers d)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description_eq : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description d z =
    d.gen (List.replicate (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description_poly : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data),
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description d)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description_shape`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description_shape : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.description d z =
    Turing.pairEncode
      (d.circuit (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z)).encode
      (Complexity.BinArith.encWords
        (List.ofFn fun j =>
          BoolCircuit.encodeNat
            (d.output (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) j)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.eval_unary_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.eval_unary_poly : ∀
  (p : Complexity.PolyExpr),
  Complexity.PolyTimeComputable fun z =>
    List.replicate (p.eval (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z)) true
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.idealB_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.idealB_eq : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (coins : Complexity.PolyExpr)
  (F : TCSlib.Cryptography.SecureComputation.Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
  (y : Fin (F.inB.eval n) → Bool)
  (r : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator d coins).Coins n),
  F.idealB (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator d coins) n x y r =
    Turing.pairEncode
      { x := List.replicate n true,
          z :=
            Turing.pairEncode (List.ofFn y)
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt d n (List.ofFn r)),
          r := [],
          received :=
            [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt d n (List.ofFn r)
                (List.ofFn (F.f n x y).2)] }.encode
      (List.ofFn (F.f n x y).1)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  ℕ → List Bool → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt_eq : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (r f : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt d n r f =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message
      (TCSlib.Cryptography.SecureComputation.nestedSpecial d.E₁ d.E₂ n) (d.circuit n) (d.seed n r) (d.inA.eval n)
      (d.outLen.eval n) (d.output n) fun j => f.getD (↑j) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt_ofFn`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt_ofFn : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (r : List Bool)
  (f : Fin (d.outLen.eval n) → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt d n r (List.ofFn f) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message
      (TCSlib.Cryptography.SecureComputation.nestedSpecial d.E₁ d.E₂ n) (d.circuit n) (d.seed n r) (d.inA.eval n)
      (d.outLen.eval n) (d.output n) f
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message_eq : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message d z =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt d
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) (Complexity.NUPPT.inCoins z)
      (Complexity.pairSndD (Complexity.NUPPT.inArg z))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message_layout : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (n : ℕ) (y f advice r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message d
      (Complexity.NUPPT.layout (List.replicate n true) (Turing.pairEncode y f) advice r) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt d n r f
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message_poly : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data),
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message d)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message_poly._proof_1_1 : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (z : List Bool),
  d.inA.eval (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) +
        d.inB.eval (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) ≤
      d.inputs.eval (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) →
    ¬d.inA.eval (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) ≤
          d.inputs.eval (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) →
      False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter : List Bool → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z = (Complexity.NUPPT.inParam z).length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter_layout : ∀ (n : ℕ)
  (arg advice coins : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter
      (Complexity.NUPPT.layout (List.replicate n true) arg advice coins) =
    n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter_unary_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter_unary_poly : Complexity.PolyTimeComputable
  fun z => List.replicate (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.parameter z) true
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data →
  Complexity.PolyExpr → Complexity.NUPPT
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_coins`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_coins : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (coins : Complexity.PolyExpr),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator d coins).coins = coins
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_eq : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (coins : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator d coins =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.simulator ⋯ ⋯ coins
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_runAt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_runAt : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (coins : Complexity.PolyExpr) (n : ℕ)
  (y f : List Bool)
  (r : (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator d coins).Coins n),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator d coins).runAt n (Turing.pairEncode y f)
      r =
    { x := List.replicate n true,
        z :=
          Turing.pairEncode y
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt d n (List.ofFn r)),
        r := [],
        received :=
          [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt d n (List.ofFn r) f] }.encode
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_runAtL`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_runAtL : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (coins : Complexity.PolyExpr) (n : ℕ)
  (y f r : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator d coins).runAtL n
      (Turing.pairEncode y f) r =
    { x := List.replicate n true,
        z := Turing.pairEncode y (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt d n r),
        r := [],
        received := [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt d n r f] }.encode
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_uniform`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator_uniform : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data) (coins : Complexity.PolyExpr),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.simulator d coins).Uniform
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.view_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.view_poly : ∀
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Data),
  Complexity.PolyTimeComputable
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator.raw
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.message d)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answers d))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulatorFactory.exists_data`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulatorFactory.exists_data : ∀
  (E₁ E₂ : List Bool → List Bool),
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ (bound inputs inA inB outLen : Complexity.PolyExpr) (gen : List Bool → List Bool),
        Complexity.PolyTimeComputable gen →
          ∀ (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ),
            (∀ (n : ℕ),
                gen (List.replicate n true) =
                  Turing.pairEncode (circuit n).encode
                    (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
              (∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                (∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                  (∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                    ∀
                      (seed :
                        (n : ℕ) →
                          List Bool →
                            TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                              ((Fin n → Bool) × (Fin n → Bool))),
                      (∀ (n : ℕ) (r : List Bool),
                          ∀ v < (circuit n).size,
                            ∀ (b : Bool),
                              TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
                                r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                        (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                            (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                            ((seed n r).2.1 i a).1 t =
                              r.getD
                                (2 * bound.eval n * n +
                                    (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                  ↑t)
                                false) →
                          (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                              (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                              ((seed n r).2.1 i a).2 t =
                                r.getD
                                  (2 * bound.eval n * n +
                                        (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                      n +
                                    ↑t)
                                  false) →
                            (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                (a : Fin (circuit n).gates[i].args.length → Bool)
                                (t : Fin (circuit n).gates[i].args.length),
                                ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                              ∃ d,
                                (∀ (n : ℕ) (r : List Bool),
                                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.answersAt d n r =
                                      List.ofFn
                                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers
                                          (circuit n) (seed n r) (inA.eval n) (inB.eval n))) ∧
                                  ∀ (n : ℕ) (r f : List Bool),
                                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.messageAt d n r
                                        f =
                                      TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message
                                        (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (circuit n)
                                        (seed n r) (inA.eval n) (outLen.eval n) (output n) fun j => f.getD (↑j) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulatorFactory.exists_simulator`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulatorFactory.exists_simulator : ∀
  (E₁ E₂ : List Bool → List Bool),
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ (bound inputs inA inB outLen : Complexity.PolyExpr) (gen : List Bool → List Bool),
        Complexity.PolyTimeComputable gen →
          ∀ (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (output : (n : ℕ) → Fin (outLen.eval n) → ℕ),
            (∀ (n : ℕ),
                gen (List.replicate n true) =
                  Turing.pairEncode (circuit n).encode
                    (Complexity.BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (output n j)))) →
              (∀ (n : ℕ), inA.eval n + inB.eval n ≤ inputs.eval n) →
                (∀ (n : ℕ) (j : Fin (outLen.eval n)), output n j < (circuit n).size) →
                  (∀ (n : ℕ) (i : Fin (circuit n).gates.length), (circuit n).gates[i].args.length ≤ 2) →
                    ∀
                      (seed :
                        (n : ℕ) →
                          List Bool →
                            TCSlib.Cryptography.SecureComputation.GarbleSeed (circuit n) (Fin n → Bool)
                              ((Fin n → Bool) × (Fin n → Bool))),
                      (∀ (n : ℕ) (r : List Bool),
                          ∀ v < (circuit n).size,
                            ∀ (b : Bool),
                              TCSlib.Cryptography.SecureComputation.keyAt (circuit n) (seed n r) v b = fun t =>
                                r.getD ((b.toNat * bound.eval n + v) * n + ↑t) false) →
                        (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                            (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                            ((seed n r).2.1 i a).1 t =
                              r.getD
                                (2 * bound.eval n * n +
                                    (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                  ↑t)
                                false) →
                          (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                              (a : Fin (circuit n).gates[i].args.length → Bool) (t : Fin n),
                              ((seed n r).2.1 i a).2 t =
                                r.getD
                                  (2 * bound.eval n * n +
                                        (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                      n +
                                    ↑t)
                                  false) →
                            (∀ (n : ℕ) (r : List Bool) (i : Fin (circuit n).gates.length)
                                (a : Fin (circuit n).gates[i].args.length → Bool)
                                (t : Fin (circuit n).gates[i].args.length),
                                ((seed n r).2.2 i) a t = (a t ^^ r.getD (10 * bound.eval n * n + 2 * ↑i + ↑t) false)) →
                              ∀ (coins : Complexity.PolyExpr),
                                ∃ SB,
                                  SB.Uniform ∧
                                    SB.coins = coins ∧
                                      (∀ (n : ℕ) (y f r : List Bool),
                                          SB.runAtL n (Turing.pairEncode y f) r =
                                            { x := List.replicate n true,
                                                z :=
                                                  Turing.pairEncode y
                                                    (List.ofFn
                                                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers
                                                        (circuit n) (seed n r) (inA.eval n) (inB.eval n))),
                                                r := [],
                                                received :=
                                                  [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message
                                                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n)
                                                      (circuit n) (seed n r) (inA.eval n) (outLen.eval n) (output n)
                                                      fun j => f.getD (↑j) false] }.encode) ∧
                                        ∀ (F : TCSlib.Cryptography.SecureComputation.Functionality) (n : ℕ)
                                          (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
                                          (r : SB.Coins n),
                                          F.idealB SB n x y r =
                                            Turing.pairEncode
                                              { x := List.replicate n true,
                                                  z :=
                                                    Turing.pairEncode (List.ofFn y)
                                                      (List.ofFn
                                                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers
                                                          (circuit n) (seed n (List.ofFn r)) (inA.eval n)
                                                          (inB.eval n))),
                                                  r := [],
                                                  received :=
                                                    [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message
                                                        (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n)
                                                        (circuit n) (seed n (List.ofFn r)) (inA.eval n) (outLen.eval n)
                                                        (output n) fun j =>
                                                        (List.ofFn (F.f n x y).2).getD (↑j) false] }.encode
                                              (List.ofFn (F.f n x y).1)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.argKeys_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.argKeys_poly : ∀ (inputs width : List Bool → ℕ)
  (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
  (s :
    (z : List Bool) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
        ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
  (i : (z : List Bool) → Fin (C z).gates.length) (a : (z : List Bool) → Fin (C z).gates[i z].args.length → Bool),
  (∀ (z : List Bool), (C z).gates[i z].args.length ≤ 2) →
    (Complexity.PolyTimeComputable fun z => [decide ((C z).gates[i z].args.length = 0)]) →
      (Complexity.PolyTimeComputable fun z => [decide ((C z).gates[i z].args.length = 1)]) →
        (Complexity.PolyTimeComputable fun z =>
            List.ofFn
              (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) ((C z).gates[i z].args.getD 0 0)
                ((List.ofFn (a z)).getD 0 false))) →
          (Complexity.PolyTimeComputable fun z =>
              List.ofFn
                (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) ((C z).gates[i z].args.getD 1 0)
                  ((List.ofFn (a z)).getD 1 false))) →
            Complexity.PolyTimeComputable fun z =>
              Complexity.BinArith.encWords
                (List.map List.ofFn (TCSlib.Cryptography.SecureComputation.argKeys (C z) (s z) (i z) (a z)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.argKeys_small`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.argKeys_small : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  C.gates[i].args.length ≤ 2 →
    Complexity.BinArith.encWords (List.map List.ofFn (TCSlib.Cryptography.SecureComputation.argKeys C s i a)) =
      if C.gates[i].args.length = 0 then []
      else
        if C.gates[i].args.length = 1 then
          Turing.pairEncode
            (List.ofFn
              (TCSlib.Cryptography.SecureComputation.keyAt C s (C.gates[i].args.getD 0 0) ((List.ofFn a).getD 0 false)))
            []
        else
          Turing.pairEncode
            (List.ofFn
              (TCSlib.Cryptography.SecureComputation.keyAt C s (C.gates[i].args.getD 0 0) ((List.ofFn a).getD 0 false)))
            (Turing.pairEncode
              (List.ofFn
                (TCSlib.Cryptography.SecureComputation.keyAt C s (C.gates[i].args.getD 1 0)
                  ((List.ofFn a).getD 1 false)))
              [])
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.argKeys_small._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.argKeys_small._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.argKeys_small._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.argKeys_small._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.fixedTable_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.fixedTable_poly : ∀ {α : Type} (enum : List α)
  (row : α → List Bool → List Bool),
  (∀ (a : α), Complexity.PolyTimeComputable (row a)) →
    Complexity.PolyTimeComputable fun z => Complexity.BinArith.encWords (List.map (fun a => row a z) enum)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.garbledRow_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.garbledRow_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ (inputs width : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
        (s :
          (z : List Bool) →
            TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
              ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
        (i : (z : List Bool) → Fin (C z).gates.length) (a : (z : List Bool) → Fin (C z).gates[i z].args.length → Bool),
        (∀ (z : List Bool), (C z).gates[i z].args.length ≤ 2) →
          (Complexity.PolyTimeComputable fun z =>
              Complexity.BinArith.encWords
                (List.map List.ofFn (TCSlib.Cryptography.SecureComputation.argKeys (C z) (s z) (i z) (a z)))) →
            (Complexity.PolyTimeComputable fun z =>
                List.ofFn
                  (TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) (inputs z + ↑(i z))
                    (TCSlib.Cryptography.SecureComputation.gateOut (C z).gates[i z] (a z)))) →
              (Complexity.PolyTimeComputable fun z => List.ofFn ((s z).2.1 (i z) (a z)).1) →
                (Complexity.PolyTimeComputable fun z => List.ofFn ((s z).2.1 (i z) (a z)).2) →
                  Complexity.PolyTimeComputable fun z =>
                    TCSlib.Cryptography.SecureComputation.garbledRow
                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)) (C z) (s z) (i z) (a z)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.garbledRow_poly._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.garbledRow_poly._proof_1 : ∀
  (inputs : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z)) (z : List Bool),
  ¬(C z).gates.length ≤ (C z).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.gateKind_test_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.gateKind_test_poly : ∀
  (k : List Bool → BoolCircuit.GateKind),
  (Complexity.PolyTimeComputable fun z => (k z).encode) →
    ∀ (tag : BoolCircuit.GateKind), Complexity.PolyTimeComputable fun z => [decide (k z = tag)]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.gateOut_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.gateOut_poly : ∀
  (g : List Bool → BoolCircuit.DAGGate) (a : (z : List Bool) → Fin (g z).args.length → Bool),
  (∀ (z : List Bool), (g z).args.length ≤ 2) →
    (Complexity.PolyTimeComputable fun z => [decide ((g z).kind = BoolCircuit.GateKind.and)]) →
      (Complexity.PolyTimeComputable fun z => [decide ((g z).kind = BoolCircuit.GateKind.or)]) →
        (Complexity.PolyTimeComputable fun z => [decide ((g z).args.length = 0)]) →
          (Complexity.PolyTimeComputable fun z => [decide ((g z).args.length = 1)]) →
            (Complexity.PolyTimeComputable fun z => [(List.ofFn (a z)).getD 0 false]) →
              (Complexity.PolyTimeComputable fun z => [(List.ofFn (a z)).getD 1 false]) →
                Complexity.PolyTimeComputable fun z => [TCSlib.Cryptography.SecureComputation.gateOut (g z) (a z)]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.gateOut_small`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.gateOut_small : ∀ (g : BoolCircuit.DAGGate)
  (a : Fin g.args.length → Bool),
  g.args.length ≤ 2 →
    TCSlib.Cryptography.SecureComputation.gateOut g a =
      if g.kind = BoolCircuit.GateKind.and then
        if g.args.length = 0 then true
        else
          if g.args.length = 1 then (List.ofFn a).getD 0 false
          else (List.ofFn a).getD 0 false && (List.ofFn a).getD 1 false
      else
        if g.kind = BoolCircuit.GateKind.or then
          if g.args.length = 0 then false
          else
            if g.args.length = 1 then (List.ofFn a).getD 0 false
            else (List.ofFn a).getD 0 false || (List.ofFn a).getD 1 false
        else
          !if g.args.length = 0 then true
            else
              if g.args.length = 1 then (List.ofFn a).getD 0 false
              else (List.ofFn a).getD 0 false && (List.ofFn a).getD 1 false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.gateOut_small._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.gateOut_small._proof_1_1 : ∀ (args : List ℕ),
  args.length + 1 + 1 + 1 ≤ 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc : (List Bool → List Bool) →
  (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_eq : ∀
  (E₁ E₂ : List Bool → List Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc E₁ E₂ z =
    if Complexity.pairFstD z = [] then Complexity.pairFstD (Complexity.pairSndD z)
    else
      if Complexity.pairSndD (Complexity.pairFstD z) = [] then
        TCSlib.Cryptography.SecureComputation.spEncStr E₁ (Complexity.pairFstD (Complexity.pairFstD z))
          (Complexity.pairFstD (Complexity.pairSndD z))
          (Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD z)))
      else
        if Complexity.pairSndD (Complexity.pairSndD (Complexity.pairFstD z)) = [] then
          TCSlib.Cryptography.SecureComputation.spEncStr E₂ (Complexity.pairFstD (Complexity.pairFstD z))
            (TCSlib.Cryptography.SecureComputation.spEncStr E₁
              (Complexity.pairFstD (Complexity.pairSndD (Complexity.pairFstD z)))
              (Complexity.pairFstD (Complexity.pairSndD z))
              (Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD z))))
            (Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD z)))
        else []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc E₁ E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_vectors`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_vectors : ∀ {n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (ks : List (Fin n → Bool)),
  ks.length ≤ 2 →
    ∀ (o : Fin n → Bool) (r : (Fin n → Bool) × (Fin n → Bool)),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc E₁ E₂
          (Turing.pairEncode (Complexity.BinArith.encWords (List.map List.ofFn ks))
            (Turing.pairEncode (List.ofFn o) (Turing.pairEncode (List.ofFn r.1) (List.ofFn r.2)))) =
        (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc ks o r
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_vectors._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_vectors._proof_1_4 : ∀ {n : ℕ}
  (ks tail : List (Fin n → Bool)), tail.length + 1 + 1 + 1 ≤ 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_vectors._simp_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_vectors._simp_1_3 : ∀
  (x y : List Bool), (Turing.pairEncode x y = []) = False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_vectors.match_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc_vectors.match_1_1 : ∀ {n : ℕ}
  (motive : (ks : List (Fin n → Bool)) → ks.length ≤ 2 → Prop) (ks : List (Fin n → Bool)) (hks : ks.length ≤ 2),
  (∀ (x : [].length ≤ 2), motive [] x) →
    (∀ (k : Fin n → Bool) (x : [k].length ≤ 2), motive [k] x) →
      (∀ (k₁ k₂ : Fin n → Bool) (x : [k₁, k₂].length ≤ 2), motive [k₁, k₂] x) →
        (∀ (head head_1 head_2 : Fin n → Bool) (tail : List (Fin n → Bool))
            (h : (head :: head_1 :: head_2 :: tail).length ≤ 2), motive (head :: head_1 :: head_2 :: tail) h) →
          motive ks hks
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly : ∀ (arity : List Bool → ℕ)
  (enum : (l : ℕ) → List (Fin l → Bool)) (row : (l : ℕ) → (Fin l → Bool) → List Bool → List Bool),
  (∀ (z : List Bool), arity z ≤ 2) →
    (Complexity.PolyTimeComputable fun z => [decide (arity z = 0)]) →
      (Complexity.PolyTimeComputable fun z => [decide (arity z = 1)]) →
        (∀ l ≤ 2, ∀ (a : Fin l → Bool), Complexity.PolyTimeComputable (row l a)) →
          Complexity.PolyTimeComputable fun z =>
            Complexity.BinArith.encWords (List.map (fun a => row (arity z) a z) (enum (arity z)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_1 : ¬0 ≤ 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_2 : ¬1 ≤ 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_3 : ¬2 ≤ 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_4 : ∀
  (arity : List Bool → ℕ) (z : List Bool) (k : ℕ), arity z = k → arity z ≤ 2 → ¬k ≤ 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_5`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.smallArityTable_poly._proof_1_5 : ∀
  (arity : List Bool → ℕ) (z : List Bool) (k : ℕ), arity z = k → k ≤ 2 → ¬(k = 0 ∨ k = 1 ∨ k = 2) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.spEncStr_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.spEncStr_poly : ∀
  {E k m r : List Bool → List Bool},
  Complexity.PolyTimeComputable E →
    Complexity.PolyTimeComputable k →
      Complexity.PolyTimeComputable m →
        Complexity.PolyTimeComputable r →
          Complexity.PolyTimeComputable fun z => TCSlib.Cryptography.SecureComputation.spEncStr E (k z) (m z) (r z)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord_description`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord_description : ∀
  (description : List Bool → List Bool) (z : List Bool) {m : ℕ} (C : BoolCircuit.DAGCircuit m) (outs : List Bool),
  description z = Turing.pairEncode C.encode outs →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord description z =
      Complexity.BinArith.encWords
        (List.map TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord C.gates)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord_eq : ∀
  (description : List Bool → List Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord description z =
    Complexity.pairSndD
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.readCircuit
        (Complexity.pairFstD (description z)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord_poly : ∀
  {description : List Bool → List Bool},
  Complexity.PolyTimeComputable description →
    Complexity.PolyTimeComputable
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.gatesWord description)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.tables_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.tables_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ (width bound inputs : List Bool → ℕ) (description outs coins : List Bool → List Bool),
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              Complexity.PolyTimeComputable description →
                Complexity.PolyTimeComputable coins →
                  ∀ (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z))
                    (s :
                      (z : List Bool) →
                        TCSlib.Cryptography.SecureComputation.GarbleSeed (C z) (Fin (width z) → Bool)
                          ((Fin (width z) → Bool) × (Fin (width z) → Bool))),
                    (∀ (z : List Bool), description z = Turing.pairEncode (C z).encode (outs z)) →
                      (∀ (z : List Bool) (i : Fin (C z).gates.length), (C z).gates[i].args.length ≤ 2) →
                        (∀ (z : List Bool),
                            ∀ v < (C z).size,
                              ∀ (b : Bool),
                                TCSlib.Cryptography.SecureComputation.keyAt (C z) (s z) v b = fun t =>
                                  (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
                          (∀ (z : List Bool) (i : Fin (C z).gates.length) (a : Fin (C z).gates[i].args.length → Bool)
                              (t : Fin (width z)),
                              ((s z).2.1 i a).1 t =
                                (coins z).getD
                                  (2 * bound z * width z +
                                      (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                        (2 * width z) +
                                    ↑t)
                                  false) →
                            (∀ (z : List Bool) (i : Fin (C z).gates.length) (a : Fin (C z).gates[i].args.length → Bool)
                                (t : Fin (width z)),
                                ((s z).2.1 i a).2 t =
                                  (coins z).getD
                                    (2 * bound z * width z +
                                          (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                            (2 * width z) +
                                        width z +
                                      ↑t)
                                    false) →
                              (∀ (z : List Bool) (i : Fin (C z).gates.length)
                                  (a : Fin (C z).gates[i].args.length → Bool) (t : Fin (C z).gates[i].args.length),
                                  ((s z).2.2 i) a t =
                                    (a t ^^ (coins z).getD (10 * bound z * width z + 2 * ↑i + ↑t) false)) →
                                Complexity.PolyTimeComputable fun z =>
                                  Complexity.BinArith.encWords
                                    (List.ofFn fun i =>
                                      Complexity.BinArith.encWords
                                        (TCSlib.Cryptography.SecureComputation.garbledTable
                                          (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)) (C z)
                                          (s z) i))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.tables_poly._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.tables_poly._proof_1 : ∀
  (inputs : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z)) (z : List Bool),
  ¬(C z).gates.length ≤ (C z).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.tables_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram.tables_poly._proof_1_1 : ∀
  (inputs : List Bool → ℕ) (C : (z : List Bool) → BoolCircuit.DAGCircuit (inputs z)) (z : List Bool)
  (i : Fin (C z).gates.length), ¬↑i < (C z).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridChain.endpoint_negligible`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridChain.endpoint_negligible : ∀ {inputs : ℕ → ℕ}
  {Z : ℕ → Type u_1} {σ : ℕ → Type u_2} [inst : (n : ℕ) → Fintype (σ n)]
  (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr),
  (∀ (n : ℕ), (C n).size ≤ S.eval n) →
    ∀ (v : (n : ℕ) → Z n → ℕ → Bool),
      (∀ (n : ℕ) (i : Fin (C n).gates.length), (C n).gates[i].args.length ≤ 2) →
        (∀ (n : ℕ) (z : Z n) (i : Fin (C n).gates.length),
            TCSlib.Cryptography.SecureComputation.gateOut (C n).gates[i]
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues (C n) (v n z) i) =
              v n z (inputs n + ↑i)) →
          ∀ (H : (n : ℕ) → Z n → ℕ → σ n → List Bool),
            (∀ (n : ℕ) (z : Z n) (t t' : ℕ),
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit (C n) (v n z) t =
                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit (C n) (v n z) t' →
                  H n z t = H n z t') →
              ∀ (D : Complexity.NUPPT) {μ : ℕ → ℝ},
                TCSlib.Cryptography.Negligible μ →
                  (∀ (n : ℕ), 0 ≤ μ n) →
                    (∀ (n : ℕ) (z : Z n) (i : Fin (C n).gates.length) (p : Fin (C n).gates[i].args.length),
                        ↑p < 2 →
                          TCSlib.Cryptography.distAdv (H n z (2 * ↑i + ↑p)) (H n z (2 * ↑i + ↑p + 1))
                              (D.distinguisherL n) ≤
                            μ n) →
                      ∃ ε,
                        TCSlib.Cryptography.Negligible ε ∧
                          ∀ (n : ℕ) (z : Z n),
                            TCSlib.Cryptography.distAdv (H n z 0) (H n z (2 * (C n).gates.length))
                                (D.distinguisherL n) ≤
                              ε n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridChain.endpoint_negligible._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridChain.endpoint_negligible._proof_1 : ∀
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (n : ℕ),
  ¬(C n).gates.length ≤ (C n).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridChain.endpoint_negligible._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridChain.endpoint_negligible._proof_1_1 : ∀
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr) (n : ℕ),
  inputs n + (C n).gates.length ≤ S.eval n → ¬2 * (C n).gates.length ≤ 2 * S.eval n → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.activeAnswers_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.activeAnswers_relabel : ∀
  {inputs width : ℕ} {ρ : Type} (C : BoolCircuit.DAGCircuit inputs)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (v : ℕ → Bool) (first count : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) first count =
    fun t => TCSlib.Cryptography.SecureComputation.keyAt C s (first + ↑t.divNat) (v (first + ↑t.divNat)) t.modNat
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.decodePair_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.decodePair_relabel : ∀ {inputs width : ℕ}
  {ρ : Type} (C : BoolCircuit.DAGCircuit inputs)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (v : ℕ → Bool) (w : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) w (v w) =
    (TCSlib.Cryptography.SecureComputation.keyAt C s w false, TCSlib.Cryptography.SecureComputation.keyAt C s w true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message : {inputs width : ℕ} →
  {ρ : Type} →
    TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ →
      (C : BoolCircuit.DAGCircuit inputs) →
        TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ →
          ℕ → (outLen : ℕ) → (Fin outLen → ℕ) → (ℕ → Bool) → ℕ → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_end`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_end : ∀ {inputs width : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v
      (2 * C.gates.length) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message M C s inA outLen output fun j =>
      v (output j)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_eq : ∀ {inputs width : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v stage =
    Turing.pairEncode
      (Complexity.BinArith.encWords
        (List.ofFn fun i =>
          Complexity.BinArith.encWords
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C s
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v stage) i)))
      (Turing.pairEncode
        (Complexity.BinArith.encWords
          (List.ofFn fun w => List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (↑w) false)))
        (Complexity.BinArith.encWords
          (List.ofFn fun j =>
            Turing.pairEncode
              (List.ofFn
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair C s (output j)
                    (v (output j))).1)
              (List.ofFn
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair C s (output j)
                    (v (output j))).2))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_relabel : ∀ {inputs width : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool),
  Turing.pairEncode
      (Complexity.BinArith.encWords
        (List.ofFn fun i => Complexity.BinArith.encWords (TCSlib.Cryptography.SecureComputation.garbledTable M C s i)))
      (Turing.pairEncode
        (Complexity.BinArith.encWords
          (List.ofFn fun w => List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (↑w) (v ↑w))))
        (Complexity.BinArith.encWords
          (List.ofFn fun j =>
            Turing.pairEncode (List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (output j) false))
              (List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (output j) true))))) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) inA outLen output v 0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample : {inputs width : ℕ} →
  {ρ : Type} →
    TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ →
      (C : BoolCircuit.DAGCircuit inputs) →
        TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ →
          ℕ →
            ℕ →
              (outLen : ℕ) →
                (Fin outLen → ℕ) → (ℕ → Bool) → List Bool → List Bool → List Bool → List Bool → ℕ → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_end`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_end : ∀ {inputs width : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (commonInput bobInput bobCoins aliceOutput : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C s inA inB outLen output v
      commonInput bobInput bobCoins aliceOutput (2 * C.gates.length) =
    Turing.pairEncode
      { x := commonInput,
          z :=
            Turing.pairEncode bobInput
              (List.ofFn (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s inA inB)),
          r := bobCoins,
          received :=
            [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message M C s inA outLen output fun j =>
                v (output j)] }.encode
      aliceOutput
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_eq : ∀ {inputs width : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (commonInput bobInput bobCoins aliceOutput : List Bool)
  (stage : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C s inA inB outLen output v
      commonInput bobInput bobCoins aliceOutput stage =
    Turing.pairEncode
      { x := commonInput,
          z :=
            Turing.pairEncode bobInput
              (List.ofFn (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s inA inB)),
          r := bobCoins,
          received :=
            [TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v
                stage] }.encode
      aliceOutput
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_relabel : ∀ {inputs width : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (commonInput bobInput bobCoins aliceOutput : List Bool),
  Turing.pairEncode
      { x := commonInput,
          z :=
            Turing.pairEncode bobInput
              (List.ofFn fun t =>
                TCSlib.Cryptography.SecureComputation.keyAt C s (inA + ↑t.divNat) (v (inA + ↑t.divNat)) t.modNat),
          r := bobCoins,
          received :=
            [Turing.pairEncode
                (Complexity.BinArith.encWords
                  (List.ofFn fun i =>
                    Complexity.BinArith.encWords (TCSlib.Cryptography.SecureComputation.garbledTable M C s i)))
                (Turing.pairEncode
                  (Complexity.BinArith.encWords
                    (List.ofFn fun w => List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (↑w) (v ↑w))))
                  (Complexity.BinArith.encWords
                    (List.ofFn fun j =>
                      Turing.pairEncode (List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (output j) false))
                        (List.ofFn (TCSlib.Cryptography.SecureComputation.keyAt C s (output j) true)))))] }.encode
      aliceOutput =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) inA inB outLen output v
      commonInput bobInput bobCoins aliceOutput 0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridSecurity.endpoint_negligible`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridSecurity.endpoint_negligible : ∀ {I : ℕ → Type}
  [(n : ℕ) → Fintype (I n)] {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n))
  (S A B O R : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (output : (n : ℕ) → Fin (O.eval n) → ℕ)
  (bobWord aliceWord : (n : ℕ) → I n → List Bool),
  (∀ (n : ℕ), (C n).size ≤ S.eval n) →
    (∀ (n : ℕ), (C n).IsFaninTwo) →
      (∀ (n : ℕ) (z : I n) (i : Fin (C n).gates.length),
          TCSlib.Cryptography.SecureComputation.gateOut (C n).gates[i]
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues (C n) (v n z) i) =
            v n z (inputs n + ↑i)) →
        (∀ (n : ℕ) (j : Fin (O.eval n)), ∀ g ∈ (C n).gates, output n j ∉ g.args) →
          (∀ (n : ℕ) (z : I n), (bobWord n z).length ≤ B.eval n) →
            (∀ (n : ℕ) (z : I n), (aliceWord n z).length ≤ R.eval n) →
              ∀ {L : Complexity.PolyExpr} {L₂ : ℕ → ℕ}
                (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L.eval n) → Bool)
                (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
                (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
                Complexity.PolyTimeComputable E₂ →
                  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
                    (∀ (n : ℕ) (s x : Fin n → Bool),
                        E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
                      (∀ (n : ℕ) (s x : Fin n → Bool),
                          E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
                        (∀ (n : ℕ), 7 * n + 2 ≤ L.eval n) →
                          TCSlib.Cryptography.SecureComputation.SliceMultiMessageSecure G →
                            (∀ (n : ℕ) (q : List Bool) (w : Fin (C n).size) (b : Bool) (t : Fin n),
                                (seed n q).1 w b t = q.getD ((b.toNat * S.eval n + ↑w) * n + ↑t) false) →
                              (∀ (n : ℕ) (q : List Bool) (i : Fin (C n).gates.length)
                                  (a : Fin (C n).gates[↑i].args.length → Bool) (t : Fin n),
                                  ((seed n q).2.1 i a).1 t =
                                    q.getD
                                      (2 * S.eval n * n +
                                          (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                        ↑t)
                                      false) →
                                (∀ (n : ℕ) (q : List Bool) (i : Fin (C n).gates.length)
                                    (a : Fin (C n).gates[↑i].args.length → Bool) (t : Fin n),
                                    ((seed n q).2.1 i a).2 t =
                                      q.getD
                                        (2 * S.eval n * n +
                                              (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                (2 * n) +
                                            n +
                                          ↑t)
                                        false) →
                                  (∀ (n : ℕ) (q : List Bool) (i : Fin (C n).gates.length)
                                      (a : Fin (C n).gates[↑i].args.length → Bool)
                                      (t : Fin (C n).gates[↑i].args.length),
                                      ((seed n q).2.2 i) a t =
                                        (a t ^^ q.getD (10 * S.eval n * n + 2 * ↑i + ↑t) false)) →
                                    ∀ (D : Complexity.NUPPT),
                                      ∃ ε,
                                        TCSlib.Cryptography.Negligible ε ∧
                                          ∀ (n : ℕ) (z : I n),
                                            TCSlib.Cryptography.distAdv
                                                (fun r =>
                                                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                                                    (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (C n)
                                                    (seed n (List.ofFn r)) (A.eval n) (B.eval n) (O.eval n) (output n)
                                                    (v n z) (List.replicate n true) (bobWord n z) [] (aliceWord n z) 0)
                                                (fun r =>
                                                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                                                    (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (C n)
                                                    (seed n (List.ofFn r)) (A.eval n) (B.eval n) (O.eval n) (output n)
                                                    (v n z) (List.replicate n true) (bobWord n z) [] (aliceWord n z)
                                                    (2 * (C n).gates.length))
                                                (D.distinguisherL n) ≤
                                              ε n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.assignment_zero_of_two`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.assignment_zero_of_two : ∀ {l : ℕ},
  l ≤ 2 →
    ∀ (a : Fin l → Bool), (List.ofFn a).getD 0 false = false → (List.ofFn a).getD 1 false = false → a = fun x => false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit : {inputs : ℕ} →
  (C : BoolCircuit.DAGCircuit inputs) →
    (ℕ → Bool) → ℕ → ℕ → (i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_completed`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_completed : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  ↑i < cutoff → TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff phase i a = false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_first`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_first : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  (List.ofFn a).getD 0 false = true →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v (↑i) 1 i a = false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_rest`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_rest : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  (List.ofFn a).getD 0 false = false →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v (↑i) 1 i a =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_rest._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_rest._simp_1_1 : ∀ (n : ℕ),
  (n < n) = False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_zero`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_zero : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v (↑i) 0 i a =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_zero._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_zero._proof_1_1 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  ↑i < ↑i ∨ ↑i = ↑i ∧ 0 ≠ 0 ∧ (List.ofFn a).getD 0 false = true → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_end`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_end : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ),
  C.gates.length ≤ cutoff →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff phase = fun x x_1 => false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_eq : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff phase i a =
    if ↑i < cutoff ∨ ↑i = cutoff ∧ phase ≠ 0 ∧ (List.ofFn a).getD 0 false = true then false
    else TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_first_unchanged`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_first_unchanged : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (cutoff : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  ↑i ≠ cutoff ∨ (List.ofFn a).getD 0 false = false →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff 0 i a =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff 1 i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_future`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_future : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  cutoff < ↑i →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff phase i a =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_future._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_future._proof_1_1 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (cutoff phase : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  cutoff < ↑i → ↑i < cutoff ∨ ↑i = cutoff ∧ phase ≠ 0 ∧ (List.ofFn a).getD 0 false = true → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (cutoff : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  ↑i ≠ cutoff →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff 1 i a =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v (cutoff + 1) 0 i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other._proof_1_1 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (cutoff : ℕ) (i : Fin C.gates.length),
  ↑i < cutoff → ¬↑i < cutoff + 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other._proof_1_2 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (cutoff : ℕ) (i : Fin C.gates.length),
  ↑i ≠ cutoff → ¬↑i < cutoff → ¬cutoff < ↑i → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other._proof_1_3 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (cutoff : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  ↑i ≠ cutoff → ¬↑i < cutoff → ↑i < cutoff + 1 ∨ ↑i = cutoff + 1 ∧ 0 ≠ 0 ∧ (List.ofFn a).getD 0 false = true → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_unchanged`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_unchanged : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    (∀ (i : Fin C.gates.length),
        TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
          v (inputs + ↑i)) →
      ∀ (cutoff : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
        ↑i ≠ cutoff ∨ (List.ofFn a).getD 0 false = true ∨ (List.ofFn a).getD 1 false = false →
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff 1 i a =
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v (cutoff + 1) 0 i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_unchanged._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_unchanged._proof_1_1 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i : Fin C.gates.length), ¬↑i < ↑i + 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_start`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_start : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v 0 0 =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_start._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_start._proof_1_1 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  ↑i < 0 ∨ ↑i = 0 ∧ 0 ≠ 0 ∧ (List.ofFn a).getD 0 false = true → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_zero`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_zero : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  (∀ (i : Fin C.gates.length),
      TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
        v (inputs + ↑i)) →
    ∀ (cutoff phase : ℕ) (i : Fin C.gates.length),
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff phase i fun x => false) =
        false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith : {K Cipher ρ : Type} →
  [Inhabited K] →
    {inputs : ℕ} →
      TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ →
        (C : BoolCircuit.DAGCircuit inputs) →
          TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ →
            ((i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Bool) →
              (i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Cipher
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith._proof_1 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith._proof_2 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_eq : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (bit : (i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Bool) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith M C s bit i a =
    M.enc (TCSlib.Cryptography.SecureComputation.argKeys C s i a)
      (TCSlib.Cryptography.SecureComputation.keyAt C s (inputs + ↑i) (bit i a)) (s.2.1 i a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_fake`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_fake : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith M C s (fun x x_1 => false) i a =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.row M C s i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_real`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_real : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith M C s
      (fun j b => TCSlib.Cryptography.SecureComputation.gateOut C.gates[j] b) i a =
    TCSlib.Cryptography.SecureComputation.garbledRow M C s i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit : {inputs : ℕ} →
  (C : BoolCircuit.DAGCircuit inputs) →
    (ℕ → Bool) → ℕ → (i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_eq : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (t : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v t =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v (t / 2) (t % 2)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_even`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_even : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (k : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * k) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v k 0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_even._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_even._proof_1_1 : ∀ (k : ℕ),
  ¬2 * k / 2 = k → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_even._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_even._proof_1_2 : ∀ (k : ℕ),
  2 * k / 2 = k → ¬2 * k % 2 = 0 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_odd`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_odd : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (k : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * k + 1) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v k 1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_odd._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_odd._proof_1_1 : ∀ (k : ℕ),
  ¬(2 * k + 1) / 2 = k → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_odd._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_odd._proof_1_2 : ∀ (k : ℕ),
  (2 * k + 1) / 2 = k → ¬(2 * k + 1) % 2 = 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_start`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_start : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v 0 =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith : {K Cipher ρ : Type} →
  [Inhabited K] →
    {inputs : ℕ} →
      TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ →
        (C : BoolCircuit.DAGCircuit inputs) →
          TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ →
            ((i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Bool) → Fin C.gates.length → List Cipher
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_congr`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_congr : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (bit bit' : (i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Bool) (i : Fin C.gates.length),
  (∀ (a : Fin C.gates[i].args.length → Bool), bit i a = bit' i a) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C s bit i =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C s bit' i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_end`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_end : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (v : ℕ → Bool)
  (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C s
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * C.gates.length)) i =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table M C s i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_eq : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (bit : (i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Bool) (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C s bit i =
    List.map
      (fun a => TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith M C s bit i ((s.2.2 i) a))
      Finset.univ.toList
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_fake`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_fake : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C s (fun x x_1 => false) i =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.table M C s i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_real`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_real : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C s
      (fun j b => TCSlib.Cryptography.SecureComputation.gateOut C.gates[j] b) i =
    TCSlib.Cryptography.SecureComputation.garbledTable M C s i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_relabel : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.garbledTable M C s i =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v) i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_start`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_start : ∀ {K Cipher ρ : Type}
  [inst : Inhabited K] {inputs : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K Cipher ρ)
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ)
  (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.garbledTable M C s i =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith M C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v 0) i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit : {inputs : ℕ} →
  (C : BoolCircuit.DAGCircuit inputs) →
    (ℕ → Bool) → (i : Fin C.gates.length) → (Fin C.gates[i].args.length → Bool) → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit_eq : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v i a =
    (TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
        ((TCSlib.Cryptography.xorPerm
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
          a) ^^
      v (inputs + ↑i))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit_zero`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit_zero : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  (∀ (i : Fin C.gates.length),
      TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
        v (inputs + ↑i)) →
    ∀ (i : Fin C.gates.length),
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit C v i fun x => false) = false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.values_consistent`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.values_consistent : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (x : Fin inputs → Bool) (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C
        (fun w => (C.values x).getD w false) i) =
    (C.values x).getD (inputs + ↑i) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.active_label_ne`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.active_label_ne : ∀ (v u : ℕ),
  (v, false) ≠ (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.decoding_label_ne`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.decoding_label_ne : ∀ {m k : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i₀ : Fin C.gates.length),
  ∀ u ∈ C.gates[↑i₀].args,
    ∀ (outs : Fin k → ℕ),
      (∀ (j : Fin k), ∀ g ∈ C.gates, outs j ∉ g.args) → ∀ (j : Fin k) (b : Bool), (outs j, b) ≠ (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.decoding_label_ne._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.decoding_label_ne._proof_1_1 : ∀ {m k : ℕ}
  (C : BoolCircuit.DAGCircuit m) (u : ℕ) (outs : Fin k → ℕ) (j : Fin k), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.exhaustive`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.exhaustive : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ) (i : Fin C.gates.length),
  C.gates[↑i].args.Nodup →
    (∀ (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      ∀ (a : Fin C.gates[↑i].args.length → Bool) (p : Fin C.gates[↑i].args.length),
        C.gates[↑i].args[↑p] = u →
          a p = true →
            ∃ r,
              (i, r, ↑p) ∈
                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u ∧
                (perm i) ((rows i).getD r fun x => false) = a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.exhaustive._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.exhaustive._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ¬C.gates[↑i].args.length ≤ C.gates[↑i].args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.hybrid_plaintext_ne`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.hybrid_plaintext_ne : ∀ (m i₀ u j : ℕ),
  u < m + i₀ → ∀ (b : Bool), (m + j, if j < i₀ then false else b) ≠ (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.hybrid_plaintext_ne._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.hybrid_plaintext_ne._proof_1_1 : ∀
  (m i₀ u j : ℕ), u < m + i₀ → ¬j < i₀ → m + j = u → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.hybrid_plaintext_ne_of_used`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.hybrid_plaintext_ne_of_used : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i₀ : Fin C.gates.length),
  ∀ u ∈ C.gates[↑i₀].args, ∀ (j : ℕ) (b : Bool), (m + j, if j < ↑i₀ then false else b) ≠ (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.length_occurrences_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.length_occurrences_le : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ),
  (∀ (i : Fin C.gates.length), (rows i).Nodup) →
    C.IsFaninTwo →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u).length ≤
        4 * C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.length_rowSlots_le_four`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.length_rowSlots_le_four : ∀
  (g : BoolCircuit.DAGGate) (rows : List (Fin g.args.length → Bool)) (perm : Equiv.Perm (Fin g.args.length → Bool))
  (u : ℕ),
  rows.Nodup →
    g.args.length ≤ 2 →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots g rows perm u).length ≤ 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.mem_occurrences_iff`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.mem_occurrences_iff : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ) (i : Fin C.gates.length)
  (r p : ℕ),
  C.gates[↑i].args.Nodup →
    ((i, r, p) ∈ TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u ↔
      r < (rows i).length ∧
        ∃ (hp : p < C.gates[↑i].args.length),
          C.gates[↑i].args[p] = u ∧ (perm i) ((rows i).getD r fun x => false) ⟨p, hp⟩ = true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.mem_occurrences_iff._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.mem_occurrences_iff._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length) (p : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.mem_rowSlots_iff`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.mem_rowSlots_iff : ∀
  (g : BoolCircuit.DAGGate) (rows : List (Fin g.args.length → Bool)) (perm : Equiv.Perm (Fin g.args.length → Bool))
  (u r p : ℕ),
  g.args.Nodup →
    ((r, p) ∈ TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots g rows perm u ↔
      r < rows.length ∧ ∃ (hp : p < g.args.length), g.args[p] = u ∧ perm (rows.getD r fun x => false) ⟨p, hp⟩ = true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) →
        ℕ → List (Fin C.gates.length × ℕ × ℕ)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u =
    List.flatMap
      (fun i =>
        List.map (fun rp => (i, rp))
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots C.gates[↑i] (rows i) (perm i)
            u))
      (List.finRange C.gates.length)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences_nodup`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences_nodup : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u).Nodup
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded : {α : Type u_1} →
  (q : ℕ) → List α → Fin (q + 1) → Option α
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded_eq : ∀ {α : Type u_1} (q : ℕ)
  (slots : List α) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q slots j = slots[↑j]?
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded_eq_none_iff`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded_eq_none_iff : ∀ {α : Type u_1}
  (q : ℕ) (slots : List α) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q slots j = none ↔ slots.length ≤ ↑j
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded_occurrences_some_iff`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded_occurrences_some_iff : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u q : ℕ),
  (∀ (i : Fin C.gates.length), (rows i).Nodup) →
    C.IsFaninTwo →
      4 * C.gates.length ≤ q + 1 →
        ∀ (s : Fin C.gates.length × ℕ × ℕ),
          (∃ j,
              TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u) j =
                some s) ↔
            s ∈ TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded_some_iff`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded_some_iff : ∀ {α : Type u_1} (q : ℕ)
  (slots : List α),
  slots.length ≤ q + 1 →
    ∀ (a : α),
      (∃ j, TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q slots j = some a) ↔ a ∈ slots
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.per_row_unique`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.per_row_unique : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ) (i : Fin C.gates.length)
  (r p p' : ℕ),
  C.gates[↑i].args.Nodup →
    (i, r, p) ∈ TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u →
      (i, r, p') ∈ TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u →
        p = p'
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots : (g : BoolCircuit.DAGGate) →
  List (Fin g.args.length → Bool) → Equiv.Perm (Fin g.args.length → Bool) → ℕ → List (ℕ × ℕ)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots_eq : ∀ (g : BoolCircuit.DAGGate)
  (rows : List (Fin g.args.length → Bool)) (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots g rows perm u =
    List.filterMap
      (fun r =>
        Option.map (fun p => (r, ↑p))
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition g
            (perm (rows.getD r fun x => false)) u))
      (List.range rows.length)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots_nodup`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots_nodup : ∀
  (g : BoolCircuit.DAGGate) (rows : List (Fin g.args.length → Bool)) (perm : Equiv.Perm (Fin g.args.length → Bool))
  (u : ℕ), (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.rowSlots g rows perm u).Nodup
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition : (g :
    BoolCircuit.DAGGate) →
  (Fin g.args.length → Bool) → ℕ → Option (Fin g.args.length)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition._proof_1 : ∀
  (g : BoolCircuit.DAGGate), ¬g.args.length ≤ g.args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition._proof_2 : ∀
  (g : BoolCircuit.DAGGate) (p : Fin g.args.length), ↑p < g.args.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition_eq : ∀
  (g : BoolCircuit.DAGGate) (a : Fin g.args.length → Bool) (u : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition g a u =
    List.find? (fun p => decide (g.args[↑p] = u ∧ a p = true)) (List.finRange g.args.length)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition_eq_some_iff`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition_eq_some_iff : ∀
  (g : BoolCircuit.DAGGate) (a : Fin g.args.length → Bool) (u : ℕ),
  g.args.Nodup →
    ∀ (p : Fin g.args.length),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition g a u = some p ↔
        g.args[↑p] = u ∧ a p = true
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition_eq_some_iff._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition_eq_some_iff._proof_1_1 : ∀
  (g : BoolCircuit.DAGGate) (u : ℕ) (p : Fin g.args.length), ¬g.args.length ≤ g.args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selected_wire_lt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selected_wire_lt : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i₀ : Fin C.gates.length), ∀ u ∈ C.gates[↑i₀].args, u < m + ↑i₀
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    (∀ (i : Fin C.gates.length),
        TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
          v (inputs + ↑i)) →
      ∀ t < 2 * C.gates.length,
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v t =
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (t + 1) ∨
          ∃ i p, t = 2 * ↑i + ↑p ∧ ↑p < 2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases.match_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases.match_1_1 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ)
  (motive : (∃ i p, ↑i = t / 2 ∧ ↑p = t % 2 ∧ t = 2 * ↑i + ↑p ∧ ↑p < 2) → Prop)
  (x : ∃ i p, ↑i = t / 2 ∧ ↑p = t % 2 ∧ t = 2 * ↑i + ↑p ∧ ↑p < 2),
  (∀ (i : Fin C.gates.length) (p : Fin C.gates[↑i].args.length) (left : ↑i = t / 2) (left_1 : ↑p = t % 2)
      (hclock : t = 2 * ↑i + ↑p) (hpos : ↑p < 2), motive ⋯) →
    motive x
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    (∀ (i : Fin C.gates.length),
        TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
          v (inputs + ↑i)) →
      ∀ t < 2 * C.gates.length,
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v t =
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (t + 1) ∨
          ∃ i p, ↑i = t / 2 ∧ ↑p = t % 2 ∧ t = 2 * ↑i + ↑p ∧ ↑p < 2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_1 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs), ∀ t < 2 * C.gates.length, ¬t / 2 < C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_2 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ) (i : Fin C.gates.length), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_3 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ) (i : Fin C.gates.length), ↑i = t / 2 → ¬t = 2 * ↑i + t % 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_4 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ) (i : Fin C.gates.length), ¬t % 2 < 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_5`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_5 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ) (i : Fin C.gates.length), ¬(t % 2 = 0 ∨ t % 2 = 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_6`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_6 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ) (i : Fin C.gates.length),
  ¬t % 2 < C.gates[↑i].args.length → t % 2 = 0 → ¬C.gates[↑i].args.length = 0 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_7`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_7 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ) (i : Fin C.gates.length), ↑i = t / 2 → t % 2 = 0 → ¬t = 2 * ↑i → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_8`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_8 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ) (i : Fin C.gates.length),
  ¬t % 2 < C.gates[↑i].args.length → t % 2 = 1 → ¬C.gates[↑i].args.length ≤ 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_9`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases.step_cases_exact._proof_1_9 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (t : ℕ) (i : Fin C.gates.length), ↑i = t / 2 → t % 2 = 1 → ¬t = 2 * ↑i + 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index : {m : ℕ} →
  BoolCircuit.DAGCircuit m → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C =
    ((i : Fin C.gates.length) × (Fin C.gates[↑i].args.length → Bool) × Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.nonce_read`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.nonce_read : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u q : ℕ) (r : Fin (q + 1) → ρ)
  (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (half : Bool),
  (if half = true then (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce C rows s u q r i a).2
    else (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce C rows s u q r i a).1) =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick C rows s.2.2 u q ⟨i, (a, half)⟩).elim
      (if half = true then (s.2.1 i a).2 else (s.2.1 i a).1) r
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) →
        ℕ →
          (q : ℕ) → TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C → Option (Fin (q + 1))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C),
  ↑x.fst < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u q : ℕ)
  (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick C rows perm u q x =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑x.fst] x.snd.1
          u).bind
      fun p =>
      if x.snd.2 = decide (↑p ≠ 0) then
        have j :=
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows perm u x.fst x.snd.1 p;
        if h : j < q + 1 then some ⟨j, h⟩ else none
      else none
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick_iff_place`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick_iff_place : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u q : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      (∀ (i : Fin C.gates.length), (rows i).Nodup) →
        ∀ (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C) (j : Fin (q + 1)),
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick C rows perm u q x = some j ↔
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place C rows perm u q j = some x
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick_of_place`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick_of_place : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u q : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length), (rows i).Nodup) →
      ∀ (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C) (j : Fin (q + 1)),
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place C rows perm u q j = some x →
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick C rows perm u q x = some j
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) →
        ℕ →
          (q : ℕ) → Fin (q + 1) → Option (TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (s : Fin C.gates.length × ℕ × ℕ), ↑s.1 < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u q : ℕ) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place C rows perm u q j =
    Option.map (fun s => ⟨s.1, ((perm s.1) ((rows s.1).getD s.2.1 fun x => false), decide (s.2.2 ≠ 0))⟩)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u) j)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place_of_padded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place_of_padded : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u q : ℕ) (j : Fin (q + 1))
  (i : Fin C.gates.length) (r p : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u) j =
      some (i, r, p) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place C rows perm u q j =
      some ⟨i, ((perm i) ((rows i).getD r fun x => false), decide (p ≠ 0))⟩
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place_of_pick`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place_of_pick : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u q : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      ∀ (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C) (j : Fin (q + 1)),
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick C rows perm u q x = some j →
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place C rows perm u q j = some x
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords.answersA_nil`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords.answersA_nil : ∀
  (H : TCSlib.Cryptography.SecureComputation.HybridProtocol TCSlib.Cryptography.SecureComputation.otFunctionality)
  (n : ℕ) (xs ys rA rB : List Bool), H.answersA n xs ys rA rB = []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords.answersB_eq_active`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords.answersB_eq_active : ∀ {m width : ℕ}
  {ρ : Type}
  (H : TCSlib.Cryptography.SecureComputation.HybridProtocol TCSlib.Cryptography.SecureComputation.otFunctionality)
  (n : ℕ) (xs ys rA rB : List Bool) (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) (v : ℕ → Bool),
  H.calls.eval n = count * width →
    (∀ (i : Fin count), v (first + ↑i) = ys.getD (↑i) false) →
      (∀ (i : Fin count) (t : Fin width),
          (H.answersB n xs ys rA rB).getD (↑i * width + ↑t) false =
            TCSlib.Cryptography.SecureComputation.keyAt C s (first + ↑i) (ys.getD (↑i) false) t) →
        H.answersB n xs ys rA rB =
          List.ofFn
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) first count)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords.answersB_eq_active._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords.answersB_eq_active._proof_1_1 : ∀
  {m width : ℕ} {ρ : Type}
  (H : TCSlib.Cryptography.SecureComputation.HybridProtocol TCSlib.Cryptography.SecureComputation.otFunctionality)
  (n : ℕ) (xs ys rA rB : List Bool) (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) (v : ℕ → Bool),
  (H.answersB n xs ys rA rB).length = count * width →
    ∀ i < (H.answersB n xs ys rA rB).length, ¬i < count * width → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords.length_answersB`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords.length_answersB : ∀
  (H : TCSlib.Cryptography.SecureComputation.HybridProtocol TCSlib.Cryptography.SecureComputation.otFunctionality)
  (n : ℕ) (xs ys rA rB : List Bool), (H.answersB n xs ys rA rB).length = H.calls.eval n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA : Complexity.PolyExpr →
  Complexity.PolyExpr → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_eq : ∀
  (inA sizeBound : Complexity.PolyExpr) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA inA sizeBound z =
    [(Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD z))).getD
        (inA.eval (Complexity.pairFstD z).length * (Complexity.pairFstD z).length +
          (Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD z))).length)
        false,
      (Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD z))).getD
        ((sizeBound.eval (Complexity.pairFstD z).length + inA.eval (Complexity.pairFstD z).length) *
            (Complexity.pairFstD z).length +
          (Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD z))).length)
        false]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_layout : ∀
  (inA sizeBound : Complexity.PolyExpr) (n j : ℕ) (x r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA inA sizeBound
      (Turing.pairEncode (List.replicate n true) (Turing.pairEncode x (Turing.pairEncode r (List.replicate j true)))) =
    [r.getD (inA.eval n * n + j) false, r.getD ((sizeBound.eval n + inA.eval n) * n + j) false]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB z =
    [(Complexity.pairFstD (Complexity.pairSndD z)).getD
        ((Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD z))).length / (Complexity.pairFstD z).length)
        false]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_layout : ∀ (n j : ℕ) (y r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB
      (Turing.pairEncode (List.replicate n true) (Turing.pairEncode y (Turing.pairEncode r (List.replicate j true)))) =
    [y.getD (j / n) false]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputA`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputA : ∀
  (inA sizeBound : Complexity.PolyExpr),
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA inA sizeBound)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputB`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputB : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argKeys_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argKeys_relabel : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type} [inst : Inhabited K]
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.argKeys C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) i a =
    TCSlib.Cryptography.SecureComputation.argKeys C s i
      ((TCSlib.Cryptography.xorPerm
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
        a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) → (ℕ → Bool) → (i : Fin C.gates.length) → Fin C.gates[i].args.length → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ¬C.gates[i].args.length ≤ C.gates[i].args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues._proof_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues._proof_3 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues._proof_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues._proof_4 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length) (t : Fin C.gates[i].args.length), ↑t < C.gates[i].args.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues_apply`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues_apply : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) (i : Fin C.gates.length) (t : Fin C.gates[i].args.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i t = v C.gates[i].args[t]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i = fun t => v C.gates[i].args[t]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.garbledTable_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.garbledTable_relabel : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K W ρ : Type} [inst : Inhabited K]
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K W ρ)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.garbledTable M C s i =
    List.map
      (fun a =>
        have b := ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s).2.2 i) a;
        M.enc
          (TCSlib.Cryptography.SecureComputation.argKeys C
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) i b)
          (TCSlib.Cryptography.SecureComputation.keyAt C
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) (m + ↑i)
            (TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
                ((TCSlib.Cryptography.xorPerm
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
                  b) ^^
              v (m + ↑i)))
          ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s).2.1 i b))
      Finset.univ.toList
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.inputKeys_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.inputKeys_relabel : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type} [inst : Inhabited K]
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (x : Fin m → Bool),
  TCSlib.Cryptography.SecureComputation.inputKeys C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) x =
    TCSlib.Cryptography.SecureComputation.inputKeys C s fun i => x i ^^ v ↑i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.keyAt_original`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.keyAt_original : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type} [inst : Inhabited K]
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (w : ℕ) (b : Bool),
  TCSlib.Cryptography.SecureComputation.keyAt C s w b =
    TCSlib.Cryptography.SecureComputation.keyAt C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) w (b ^^ v w)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.keyAt_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.keyAt_relabel : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type} [inst : Inhabited K]
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (w : ℕ) (b : Bool),
  TCSlib.Cryptography.SecureComputation.keyAt C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) w b =
    TCSlib.Cryptography.SecureComputation.keyAt C s w (b ^^ v w)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.output_pair_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.output_pair_relabel : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type} [inst : Inhabited K]
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (w : ℕ),
  (TCSlib.Cryptography.SecureComputation.keyAt C s w false, TCSlib.Cryptography.SecureComputation.keyAt C s w true) =
    if v w = true then
      (TCSlib.Cryptography.SecureComputation.keyAt C
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) w true,
        TCSlib.Cryptography.SecureComputation.keyAt C
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) w false)
    else
      (TCSlib.Cryptography.SecureComputation.keyAt C
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) w false,
        TCSlib.Cryptography.SecureComputation.keyAt C
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) w true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (ℕ → Bool) →
      {K ρ : Type} →
        TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ → TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_coin`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_coin : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s).2.1 i a =
    s.2.1 i
      ((TCSlib.Cryptography.xorPerm
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
        a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s =
    (fun w b => s.1 w (b ^^ v ↑w), fun i a =>
      s.2.1 i
        ((TCSlib.Cryptography.xorPerm
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
          a),
      fun i =>
      Equiv.trans (s.2.2 i)
        (TCSlib.Cryptography.xorPerm
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_key : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (w : Fin C.size) (b : Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s).1 w b = s.1 w (b ^^ v ↑w)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_perm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_perm : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s).2.2 i) a =
    (TCSlib.Cryptography.xorPerm (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
      ((s.2.2 i) a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.row_relabel`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.row_relabel : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K W ρ : Type} [inst : Inhabited K]
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K W ρ)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (i : Fin C.gates.length)
  (a : Fin C.gates[i].args.length → Bool),
  M.enc
      (TCSlib.Cryptography.SecureComputation.argKeys C
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) i a)
      (TCSlib.Cryptography.SecureComputation.keyAt C
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) (m + ↑i)
        (TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
            ((TCSlib.Cryptography.xorPerm
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
              a) ^^
          v (m + ↑i)))
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s).2.1 i a) =
    TCSlib.Cryptography.SecureComputation.garbledRow M C s i
      ((TCSlib.Cryptography.xorPerm
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i))
        a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.selectedKeys_original`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.selectedKeys_original : ∀ {m k : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) {K ρ : Type} [inst : Inhabited K]
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (wire : Fin k → ℕ) (bits : Fin k → Bool),
  (List.ofFn fun j => TCSlib.Cryptography.SecureComputation.keyAt C s (wire j) (bits j)) =
    List.ofFn fun j =>
      TCSlib.Cryptography.SecureComputation.keyAt C
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed C v s) (wire j)
        (bits j ^^ v (wire j))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit : (List Bool → ℕ) →
  (List Bool → ℕ) → (List Bool → ℕ) → (List Bool → List Bool) → (l : ℕ) → (Fin l → Bool) → ℕ → List Bool → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit_eq : ∀
  (width bound gate : List Bool → ℕ) (coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool) (j : ℕ) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit width bound gate coins l a j z =
    if j < l then (List.ofFn a).getD j false ^^ (coins z).getD (10 * bound z * width z + 2 * gate z + j) false
    else false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit_of_perm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit_of_perm : ∀
  (width bound gate : List Bool → ℕ) (coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool)
  (p : Equiv.Perm (Fin l → Bool)) (z : List Bool) (j : ℕ),
  (∀ (t : Fin l), p a t = (a t ^^ (coins z).getD (10 * bound z * width z + 2 * gate z + ↑t) false)) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit width bound gate coins l a j z =
      (List.ofFn (p a)).getD j false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit_poly : ∀
  {width bound gate : List Bool → ℕ} {coins : List Bool → List Bool},
  (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
    (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (gate z) true) →
        Complexity.PolyTimeComputable coins →
          ∀ (l : ℕ) (a : Fin l → Bool) (j : ℕ),
            Complexity.PolyTimeComputable fun z =>
              [TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit width bound gate coins l
                  a j z]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentFold_eq_two`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentFold_eq_two : ∀ {l : ℕ}
  (a : Fin l → Bool),
  l ≤ 2 →
    List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a) =
      ((List.ofFn a).getD 0 false).toNat + 2 * ((List.ofFn a).getD 1 false).toNat
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentFold_eq_two._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentFold_eq_two._proof_1_1 : ∀ {l : ℕ},
  l ≤ 2 → ¬(l = 0 ∨ l = 1 ∨ l = 2) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit : (List Bool → List Bool) →
  ℕ → (List Bool → Bool) → (List Bool → Bool) → List Bool → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit_eq : ∀ (kind : List Bool → List Bool)
  (l : ℕ) (b₀ b₁ : List Bool → Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit kind l b₀ b₁ z =
    if kind z = [false, false] then if l = 0 then true else if l = 1 then b₀ z else b₀ z && b₁ z
    else
      if kind z = [false, true] then if l = 0 then false else if l = 1 then b₀ z else b₀ z || b₁ z
      else !if l = 0 then true else if l = 1 then b₀ z else b₀ z && b₁ z
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit_eq_gateOut`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit_eq_gateOut : ∀
  (g : BoolCircuit.DAGGate) (a : Fin g.args.length → Bool) (kind : List Bool → List Bool) (b₀ b₁ : List Bool → Bool)
  (z : List Bool),
  g.args.length ≤ 2 →
    kind z = g.kind.encode →
      b₀ z = (List.ofFn a).getD 0 false →
        b₁ z = (List.ofFn a).getD 1 false →
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit kind g.args.length b₀ b₁ z =
            TCSlib.Cryptography.SecureComputation.gateOut g a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit_poly : ∀
  {kind : List Bool → List Bool},
  Complexity.PolyTimeComputable kind →
    ∀ (l : ℕ) {b₀ b₁ : List Bool → Bool},
      (Complexity.PolyTimeComputable fun z => [b₀ z]) →
        (Complexity.PolyTimeComputable fun z => [b₁ z]) →
          Complexity.PolyTimeComputable fun z =>
            [TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit kind l b₀ b₁ z]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord : (List Bool → ℕ) →
  (List Bool → ℕ) → (List Bool → ℕ) → (List Bool → Bool) → (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord_eq : ∀
  (width bound vertex : List Bool → ℕ) (bit : List Bool → Bool) (coins : List Bool → List Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord width bound vertex bit coins z =
    List.ofFn fun t => (coins z).getD (((bit z).toNat * bound z + vertex z) * width z + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord_poly : ∀
  {width bound vertex : List Bool → ℕ} {bit : List Bool → Bool} {coins : List Bool → List Bool},
  Complexity.PolyTimeComputable coins →
    (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
        (Complexity.PolyTimeComputable fun z => List.replicate (vertex z) true) →
          (Complexity.PolyTimeComputable fun z => [bit z]) →
            Complexity.PolyTimeComputable
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord width bound vertex bit coins)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord : (List Bool → ℕ) →
  (List Bool → ℕ) → (List Bool → ℕ) → (List Bool → ℕ) → (List Bool → List Bool) → Bool → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord_eq : ∀
  (width bound gate index : List Bool → ℕ) (coins : List Bool → List Bool) (half : Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord width bound gate index coins half z =
    List.ofFn fun t =>
      (coins z).getD (2 * bound z * width z + (4 * gate z + index z) * (2 * width z) + half.toNat * width z + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord_poly : ∀
  {width bound gate index : List Bool → ℕ} {coins : List Bool → List Bool} (half : Bool),
  Complexity.PolyTimeComputable coins →
    (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
        (Complexity.PolyTimeComputable fun z => List.replicate (gate z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (index z) true) →
            Complexity.PolyTimeComputable
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord width bound gate index coins
                half)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord : (List Bool → List Bool) →
  (List Bool → List Bool) →
    (List Bool → ℕ) →
      (List Bool → ℕ) →
        (List Bool → ℕ) →
          (List Bool → ℕ) →
            (List Bool → List Bool) →
              (List Bool → List Bool) → (List Bool → List Bool) → (l : ℕ) → (Fin l → Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith : (List Bool → List Bool) →
  (List Bool → List Bool) →
    (List Bool → ℕ) →
      (List Bool → ℕ) →
        (List Bool → ℕ) →
          (List Bool → ℕ) →
            (List Bool → List Bool) →
              (List Bool → List Bool) → (List Bool → Bool) → (l : ℕ) → (Fin l → Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ) (args coins : List Bool → List Bool)
  (outputBit : List Bool → Bool) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z))
  (s :
    TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
  (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  C.gates[i].args.length ≤ 2 →
    gate z = ↑i →
      args z = Complexity.BinArith.encWords (List.map (fun v => List.replicate v true) C.gates[i].args) →
        (∀ v < C.size,
            ∀ (b : Bool),
              TCSlib.Cryptography.SecureComputation.keyAt C s v b = fun t =>
                (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
          (∀ (a : Fin C.gates[i].args.length → Bool) (t : Fin (width z)),
              (s.2.1 i a).1 t =
                (coins z).getD
                  (2 * bound z * width z +
                      (4 * gate z + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * width z) +
                    ↑t)
                  false) →
            (∀ (a : Fin C.gates[i].args.length → Bool) (t : Fin (width z)),
                (s.2.1 i a).2 t =
                  (coins z).getD
                    (2 * bound z * width z +
                          (4 * gate z + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * width z) +
                        width z +
                      ↑t)
                    false) →
              (∀ (a : Fin C.gates[i].args.length → Bool) (t : Fin C.gates[i].args.length),
                  (s.2.2 i) a t = (a t ^^ (coins z).getD (10 * bound z * width z + 2 * gate z + ↑t) false)) →
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith E₁ E₂ width bound inputs
                    gate args coins outputBit C.gates[i].args.length a z =
                  (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)).enc
                    (TCSlib.Cryptography.SecureComputation.argKeys C s i ((s.2.2 i) a))
                    (TCSlib.Cryptography.SecureComputation.keyAt C s (inputs z + ↑i) (outputBit z))
                    (s.2.1 i ((s.2.2 i) a))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_1 : ∀
  (inputs : List Bool → ℕ) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z)),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_1_1 : ∀
  (inputs gate : List Bool → ℕ) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z)) (i : Fin C.gates.length),
  ¬↑i < C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_1_2 : ∀
  (inputs gate : List Bool → ℕ) (args : List Bool → List Bool) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z))
  (i : Fin C.gates.length), ¬↑i < C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_1_3 : ∀
  (inputs gate : List Bool → ℕ) (args : List Bool → List Bool) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z))
  (i : Fin C.gates.length) (j : ℕ), ¬j < C.gates[i].args.length → ¬C.gates[i].args.length ≤ j → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_enc._proof_2 : ∀
  (inputs gate : List Bool → ℕ) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z)) (i : Fin C.gates.length),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_eq : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ) (args coins : List Bool → List Bool)
  (outputBit : List Bool → Bool) (l : ℕ) (a : Fin l → Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith E₁ E₂ width bound inputs gate args coins
      outputBit l a z =
    have b₀ :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit width bound gate coins l a 0;
    have b₁ :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit width bound gate coins l a 1;
    have k₀ :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord width bound
        (fun w => (Complexity.BinArith.getW (Turing.pairEncode [] (args w))).length) b₀ coins;
    have k₁ :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord width bound
        (fun w => (Complexity.BinArith.getW (Turing.pairEncode [true] (args w))).length) b₁ coins;
    have keys :=
      if l = 0 then []
      else if l = 1 then Turing.pairEncode (k₀ z) [] else Turing.pairEncode (k₀ z) (Turing.pairEncode (k₁ z) []);
    have out :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord width bound (fun w => inputs w + gate w)
        outputBit coins;
    have index := fun w => (b₀ w).toNat + 2 * (b₁ w).toNat;
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc E₁ E₂
      (Turing.pairEncode keys
        (Turing.pairEncode (out z)
          (Turing.pairEncode
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord width bound gate index coins
              false z)
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord width bound gate index coins
              true z))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ {width bound inputs gate : List Bool → ℕ} {args coins : List Bool → List Bool} {outputBit : List Bool → Bool},
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              (Complexity.PolyTimeComputable fun z => List.replicate (gate z) true) →
                Complexity.PolyTimeComputable args →
                  Complexity.PolyTimeComputable coins →
                    (Complexity.PolyTimeComputable fun z => [outputBit z]) →
                      ∀ (l : ℕ) (a : Fin l → Bool),
                        Complexity.PolyTimeComputable
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith E₁ E₂ width
                            bound inputs gate args coins outputBit l a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_value`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith_value : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ) (args coins : List Bool → List Bool)
  (outputBit : List Bool → Bool) (l : ℕ) (a : Fin l → Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith E₁ E₂ width bound inputs gate args coins
      outputBit l a z =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWordWith E₁ E₂ (fun x => width z)
      (fun x => bound z) (fun x => inputs z) (fun x => gate z) (fun x => args z) (fun x => coins z)
      (fun x => outputBit z) l a []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_eq : ∀ (E₁ E₂ : List Bool → List Bool)
  (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind args
      coins l a z =
    have b₀ :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit width bound gate coins l a 0;
    have b₁ :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.assignmentBit width bound gate coins l a 1;
    have k₀ :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord width bound
        (fun w => (Complexity.BinArith.getW (Turing.pairEncode [] (args w))).length) b₀ coins;
    have k₁ :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord width bound
        (fun w => (Complexity.BinArith.getW (Turing.pairEncode [true] (args w))).length) b₁ coins;
    have keys :=
      if l = 0 then []
      else if l = 1 then Turing.pairEncode (k₀ z) [] else Turing.pairEncode (k₀ z) (Turing.pairEncode (k₁ z) []);
    have out :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.keyWord width bound (fun w => inputs w + gate w)
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.gateBit kind l b₀ b₁) coins;
    have index := fun w => (b₀ w).toNat + 2 * (b₁ w).toNat;
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.nestedWordEnc E₁ E₂
      (Turing.pairEncode keys
        (Turing.pairEncode (out z)
          (Turing.pairEncode
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord width bound gate index coins
              false z)
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.nonceWord width bound gate index coins
              true z))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_garbledRow`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_garbledRow : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
  (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z))
  (s :
    TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
  (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  C.gates[i].args.length ≤ 2 →
    gate z = ↑i →
      kind z = C.gates[i].kind.encode →
        args z = Complexity.BinArith.encWords (List.map (fun v => List.replicate v true) C.gates[i].args) →
          (∀ v < C.size,
              ∀ (b : Bool),
                TCSlib.Cryptography.SecureComputation.keyAt C s v b = fun t =>
                  (coins z).getD ((b.toNat * bound z + v) * width z + ↑t) false) →
            (∀ (a : Fin C.gates[i].args.length → Bool) (t : Fin (width z)),
                (s.2.1 i a).1 t =
                  (coins z).getD
                    (2 * bound z * width z +
                        (4 * gate z + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * width z) +
                      ↑t)
                    false) →
              (∀ (a : Fin C.gates[i].args.length → Bool) (t : Fin (width z)),
                  (s.2.1 i a).2 t =
                    (coins z).getD
                      (2 * bound z * width z +
                            (4 * gate z + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * width z) +
                          width z +
                        ↑t)
                      false) →
                (∀ (a : Fin C.gates[i].args.length → Bool) (t : Fin C.gates[i].args.length),
                    (s.2.2 i) a t = (a t ^^ (coins z).getD (10 * bound z * width z + 2 * gate z + ↑t) false)) →
                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord E₁ E₂ width bound inputs
                      gate kind args coins C.gates[i].args.length a z =
                    TCSlib.Cryptography.SecureComputation.garbledRow
                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)) C s i ((s.2.2 i) a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_garbledRow._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_garbledRow._proof_1_1 : ∀
  (inputs gate : List Bool → ℕ) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z)) (i : Fin C.gates.length),
  ¬↑i < C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ {width bound inputs gate : List Bool → ℕ} {kind args coins : List Bool → List Bool},
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              (Complexity.PolyTimeComputable fun z => List.replicate (gate z) true) →
                Complexity.PolyTimeComputable kind →
                  Complexity.PolyTimeComputable args →
                    Complexity.PolyTimeComputable coins →
                      ∀ (l : ℕ) (a : Fin l → Bool),
                        Complexity.PolyTimeComputable
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord E₁ E₂ width bound
                            inputs gate kind args coins l a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_value`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord_value : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
  (l : ℕ) (a : Fin l → Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind args
      coins l a z =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord E₁ E₂ (fun x => width z)
      (fun x => bound z) (fun x => inputs z) (fun x => gate z) (fun x => kind z) (fun x => args z) (fun x => coins z) l
      a []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc : List Bool → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_eq : ∀ (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc w =
    decide (Complexity.pairFstD (Complexity.pairSndD w) = [])
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly : Complexity.PolyTimeComputable
  fun w => [TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc w]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.exists_machine`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.exists_machine : ∀ {β : List Bool → Type}
  (gateCode : BoolCircuit.DAGGate → List Bool) (valueCode : (x : List Bool) → List (β x) → List Bool)
  (gs : List Bool → List BoolCircuit.DAGGate) (init : (x : List Bool) → List (β x))
  (f : (x : List Bool) → BoolCircuit.DAGGate → List (β x) → β x) {F : List Bool → List Bool},
  (Complexity.PolyTimeComputable fun x => Complexity.BinArith.encWords (List.map gateCode (gs x))) →
    (Complexity.PolyTimeComputable fun x => valueCode x (init x)) →
      Complexity.PolyTimeComputable F →
        (∀ (x : List Bool) (g : BoolCircuit.DAGGate) (vs : List (β x)),
            F (Turing.pairEncode x (Turing.pairEncode (gateCode g) (valueCode x vs))) =
              valueCode x (vs ++ [f x g vs])) →
          ∀ (R B : Complexity.PolyExpr),
            (∀ (x : List Bool), (gs x).length ≤ R.eval x.length) →
              (∀ (x : List Bool),
                  ∀ i ≤ (gs x).length,
                    (Turing.pairEncode (Complexity.BinArith.encWords (List.map gateCode (List.drop i (gs x))))
                          (valueCode x (BoolCircuit.runWith (f x) (List.take i (gs x)) (init x)))).length ≤
                      B.eval x.length) →
                ∃ M A d,
                  (Turing.ModuleHost.Clean M (fun x => valueCode x (BoolCircuit.runWith (f x) (gs x) (init x)))
                      (fun x => []) fun n => A * (n + 1) ^ d) ∧
                    ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
                      |(Turing.MultiTapeTM.runFrom (Turing.Cfg.ofWords M.tm.q₀ (Turing.stateWord M.k arg))
                                v).workTapePos
                            j| ≤
                        ↑(A * (arg.length + 1) ^ d)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.orbit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.orbit_eq : ∀ {β : List Bool → Type}
  (gateCode : BoolCircuit.DAGGate → List Bool) (valueCode : (x : List Bool) → List (β x) → List Bool)
  (gs : List Bool → List BoolCircuit.DAGGate) (init : (x : List Bool) → List (β x))
  (f : (x : List Bool) → BoolCircuit.DAGGate → List (β x) → β x) (F : List Bool → List Bool),
  (∀ (x : List Bool) (g : BoolCircuit.DAGGate) (vs : List (β x)),
      F (Turing.pairEncode x (Turing.pairEncode (gateCode g) (valueCode x vs))) = valueCode x (vs ++ [f x g vs])) →
    ∀ (x : List Bool),
      ∀ i ≤ (gs x).length,
        Complexity.StateLoop.orbit
            (fun z =>
              Turing.pairEncode (Complexity.BinArith.encWords (List.map gateCode (gs z))) (valueCode z (init z)))
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step F) x i =
          Turing.pairEncode (Complexity.BinArith.encWords (List.map gateCode (List.drop i (gs x))))
            (valueCode x (BoolCircuit.runWith (f x) (List.take i (gs x)) (init x)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.orbit_eq._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.orbit_eq._proof_1_1 : ∀
  (gs : List Bool → List BoolCircuit.DAGGate) (x : List Bool) (i : ℕ),
  i + 1 ≤ (gs x).length → ¬i < (gs x).length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.orbit_eq._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.orbit_eq._proof_1_2 : ∀
  (gs : List Bool → List BoolCircuit.DAGGate) (x : List Bool) (i : ℕ),
  i + 1 ≤ (gs x).length → ¬i ≤ (gs x).length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.polyTimeComputable_runWith`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.polyTimeComputable_runWith : ∀
  {β : List Bool → Type} (gateCode : BoolCircuit.DAGGate → List Bool)
  (valueCode : (x : List Bool) → List (β x) → List Bool) (gs : List Bool → List BoolCircuit.DAGGate)
  (init : (x : List Bool) → List (β x)) (f : (x : List Bool) → BoolCircuit.DAGGate → List (β x) → β x)
  {F : List Bool → List Bool},
  (Complexity.PolyTimeComputable fun x => Complexity.BinArith.encWords (List.map gateCode (gs x))) →
    (Complexity.PolyTimeComputable fun x => valueCode x (init x)) →
      Complexity.PolyTimeComputable F →
        (∀ (x : List Bool) (g : BoolCircuit.DAGGate) (vs : List (β x)),
            F (Turing.pairEncode x (Turing.pairEncode (gateCode g) (valueCode x vs))) =
              valueCode x (vs ++ [f x g vs])) →
          ∀ (R B : Complexity.PolyExpr),
            (∀ (x : List Bool), (gs x).length ≤ R.eval x.length) →
              (∀ (x : List Bool),
                  ∀ i ≤ (gs x).length,
                    (Turing.pairEncode (Complexity.BinArith.encWords (List.map gateCode (List.drop i (gs x))))
                          (valueCode x (BoolCircuit.runWith (f x) (List.take i (gs x)) (init x)))).length ≤
                      B.eval x.length) →
                Complexity.PolyTimeComputable fun x => valueCode x (BoolCircuit.runWith (f x) (gs x) (init x))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step_eq : ∀ (F : List Bool → List Bool)
  (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step F w =
    Turing.pairEncode (Complexity.pairSndD (Complexity.pairFstD (Complexity.pairSndD w)))
      (F
        (Turing.pairEncode (Complexity.pairFstD w)
          (Turing.pairEncode (Complexity.pairFstD (Complexity.pairFstD (Complexity.pairSndD w)))
            (Complexity.pairSndD (Complexity.pairSndD w)))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step_poly : ∀ {F : List Bool → List Bool},
  Complexity.PolyTimeComputable F →
    Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.step F)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_end_eq_fake`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_end_eq_fake : ∀
  {inputs width : ℕ} {ρ : Type} {σ : Type u_1} {κ : Type u_2} [inst : Fintype σ] [inst_1 : Fintype κ]
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs)
  (seed : σ → TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (inA inB outLen : ℕ)
  (output : Fin outLen → ℕ) (v : ℕ → Bool) (result : Fin outLen → Bool),
  (∀ (j : Fin outLen), v (output j) = result j) →
    ∀ (commonInput bobInput bobCoins aliceOutput : List Bool) (D : List Bool → κ → Bool),
      TCSlib.Cryptography.acceptProb
          (fun r =>
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C (seed r) inA inB outLen
              output v commonInput bobInput bobCoins aliceOutput (2 * C.gates.length))
          D =
        TCSlib.Cryptography.acceptProb
          (fun r =>
            Turing.pairEncode
              { x := commonInput,
                  z :=
                    Turing.pairEncode bobInput
                      (List.ofFn
                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C (seed r) inA
                          inB)),
                  r := bobCoins,
                  received :=
                    [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message M C (seed r) inA outLen
                        output result] }.encode
              aliceOutput)
          D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_end_eq_ideal`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_end_eq_ideal : ∀
  {inputs width : ℕ} {ρ : Type} {σ : Type u_1} {τ : Type u_2} [inst : Fintype σ] [inst_1 : Fintype τ]
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs)
  (seed : σ → TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (inA inB outLen : ℕ)
  (output : Fin outLen → ℕ) (v : ℕ → Bool) (result : Fin outLen → Bool),
  (∀ (j : Fin outLen), v (output j) = result j) →
    ∀ (commonInput bobInput bobCoins aliceOutput : List Bool) (e : σ ≃ τ) (ideal : τ → List Bool),
      (∀ (r : σ),
          ideal (e r) =
            Turing.pairEncode
              { x := commonInput,
                  z :=
                    Turing.pairEncode bobInput
                      (List.ofFn
                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C (seed r) inA
                          inB)),
                  r := bobCoins,
                  received :=
                    [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message M C (seed r) inA outLen
                        output result] }.encode
              aliceOutput) →
        ∀ {κ : Type u_3} [inst_2 : Fintype κ] (D : List Bool → κ → Bool),
          TCSlib.Cryptography.acceptProb
              (fun r =>
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C (seed r) inA inB
                  outLen output v commonInput bobInput bobCoins aliceOutput (2 * C.gates.length))
              D =
            TCSlib.Cryptography.acceptProb ideal D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_real_eq_stage0`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_real_eq_stage0 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (S n : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    ∀ (v : ℕ → Bool),
      C.size ≤ S →
        ∀
          (seed :
            List Bool →
              TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
          (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
              (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
            (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
                ((seed q).2.1 i a).1 t =
                  q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
                    false) →
              (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
                  ((seed q).2.1 i a).2 t =
                    q.getD
                      (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n +
                        ↑t)
                      false) →
                (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool)
                    (t : Fin C.gates[i].args.length),
                    ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
                  ∀
                    (M :
                      TCSlib.Cryptography.SecureComputation.MultiEnc (Fin n → Bool) (List Bool)
                        ((Fin n → Bool) × (Fin n → Bool)))
                    (inA inB outLen : ℕ) (output : Fin outLen → ℕ)
                    (commonInput bobInput bobCoins aliceOutput : List Bool)
                    (real : (Fin (10 * S * n + 2 * S) → Bool) → List Bool),
                    (∀ (r : Fin (10 * S * n + 2 * S) → Bool),
                        real r =
                          Turing.pairEncode
                            { x := commonInput,
                                z :=
                                  Turing.pairEncode bobInput
                                    (List.ofFn fun t =>
                                      TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                        (inA + ↑t.divNat) (v (inA + ↑t.divNat)) t.modNat),
                                r := bobCoins,
                                received :=
                                  [Turing.pairEncode
                                      (Complexity.BinArith.encWords
                                        (List.ofFn fun i =>
                                          Complexity.BinArith.encWords
                                            (TCSlib.Cryptography.SecureComputation.garbledTable M C (seed (List.ofFn r))
                                              i)))
                                      (Turing.pairEncode
                                        (Complexity.BinArith.encWords
                                          (List.ofFn fun w =>
                                            List.ofFn
                                              (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r)) (↑w)
                                                (v ↑w))))
                                        (Complexity.BinArith.encWords
                                          (List.ofFn fun j =>
                                            Turing.pairEncode
                                              (List.ofFn
                                                (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                                  (output j) false))
                                              (List.ofFn
                                                (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                                  (output j) true)))))] }.encode
                            aliceOutput) →
                      ∀ {κ : Type u_1} [inst : Fintype κ] (D : List Bool → κ → Bool),
                        TCSlib.Cryptography.acceptProb real D =
                          TCSlib.Cryptography.acceptProb
                            (fun r =>
                              TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C
                                (seed (List.ofFn r)) inA inB outLen output v commonInput bobInput bobCoins aliceOutput
                                0)
                            D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_real_eq_stage0_fst`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_real_eq_stage0_fst : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (S n : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    ∀ (v : ℕ → Bool),
      C.size ≤ S →
        ∀
          (seed :
            List Bool →
              TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
          (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
              (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
            (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
                ((seed q).2.1 i a).1 t =
                  q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
                    false) →
              (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
                  ((seed q).2.1 i a).2 t =
                    q.getD
                      (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n +
                        ↑t)
                      false) →
                (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool)
                    (t : Fin C.gates[i].args.length),
                    ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
                  ∀
                    (M :
                      TCSlib.Cryptography.SecureComputation.MultiEnc (Fin n → Bool) (List Bool)
                        ((Fin n → Bool) × (Fin n → Bool)))
                    (inA inB outLen : ℕ) (output : Fin outLen → ℕ)
                    (commonInput bobInput bobCoins aliceOutput : List Bool)
                    (real : (Fin (10 * S * n + 2 * S) → Bool) → List Bool),
                    (∀ (r : Fin (10 * S * n + 2 * S) → Bool),
                        real r =
                          Turing.pairEncode
                            { x := commonInput,
                                z :=
                                  Turing.pairEncode bobInput
                                    (List.ofFn fun t =>
                                      TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                        (inA + ↑t.divNat) (v (inA + ↑t.divNat)) t.modNat),
                                r := bobCoins,
                                received :=
                                  [Turing.pairEncode
                                      (Complexity.BinArith.encWords
                                        (List.ofFn fun i =>
                                          Complexity.BinArith.encWords
                                            (TCSlib.Cryptography.SecureComputation.garbledTable M C (seed (List.ofFn r))
                                              i)))
                                      (Turing.pairEncode
                                        (Complexity.BinArith.encWords
                                          (List.ofFn fun w =>
                                            List.ofFn
                                              (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r)) (↑w)
                                                (v ↑w))))
                                        (Complexity.BinArith.encWords
                                          (List.ofFn fun j =>
                                            Turing.pairEncode
                                              (List.ofFn
                                                (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                                  (output j) false))
                                              (List.ofFn
                                                (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                                  (output j) true)))))] }.encode
                            aliceOutput) →
                      ∀ {τ : Type u_1} {κ : Type u_2} [inst : Fintype τ] [Nonempty τ] [inst_2 : Fintype κ]
                        (D : List Bool → κ → Bool),
                        TCSlib.Cryptography.acceptProb (fun r => real r.1) D =
                          TCSlib.Cryptography.acceptProb
                            (fun r =>
                              TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C
                                (seed (List.ofFn r)) inA inB outLen output v commonInput bobInput bobCoins aliceOutput
                                0)
                            D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.distAdv_end_ideal_zero`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.distAdv_end_ideal_zero : ∀
  {inputs width : ℕ} {ρ : Type} {σ : Type u_1} {τ : Type u_2} [inst : Fintype σ] [inst_1 : Fintype τ]
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs)
  (seed : σ → TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ) (inA inB outLen : ℕ)
  (output : Fin outLen → ℕ) (v : ℕ → Bool) (result : Fin outLen → Bool),
  (∀ (j : Fin outLen), v (output j) = result j) →
    ∀ (commonInput bobInput bobCoins aliceOutput : List Bool) (e : σ ≃ τ) (ideal : τ → List Bool),
      (∀ (r : σ),
          ideal (e r) =
            Turing.pairEncode
              { x := commonInput,
                  z :=
                    Turing.pairEncode bobInput
                      (List.ofFn
                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C (seed r) inA
                          inB)),
                  r := bobCoins,
                  received :=
                    [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message M C (seed r) inA outLen
                        output result] }.encode
              aliceOutput) →
        ∀ {κ : Type u_3} [inst_2 : Fintype κ] (D : List Bool → κ → Bool),
          TCSlib.Cryptography.distAdv
              (fun r =>
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C (seed r) inA inB
                  outLen output v commonInput bobInput bobCoins aliceOutput (2 * C.gates.length))
              ideal D =
            0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.distAdv_real_stage0_zero`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.distAdv_real_stage0_zero : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (S n : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    ∀ (v : ℕ → Bool),
      C.size ≤ S →
        ∀
          (seed :
            List Bool →
              TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
          (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
              (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
            (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
                ((seed q).2.1 i a).1 t =
                  q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
                    false) →
              (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
                  ((seed q).2.1 i a).2 t =
                    q.getD
                      (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n +
                        ↑t)
                      false) →
                (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool)
                    (t : Fin C.gates[i].args.length),
                    ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
                  ∀
                    (M :
                      TCSlib.Cryptography.SecureComputation.MultiEnc (Fin n → Bool) (List Bool)
                        ((Fin n → Bool) × (Fin n → Bool)))
                    (inA inB outLen : ℕ) (output : Fin outLen → ℕ)
                    (commonInput bobInput bobCoins aliceOutput : List Bool)
                    (real : (Fin (10 * S * n + 2 * S) → Bool) → List Bool),
                    (∀ (r : Fin (10 * S * n + 2 * S) → Bool),
                        real r =
                          Turing.pairEncode
                            { x := commonInput,
                                z :=
                                  Turing.pairEncode bobInput
                                    (List.ofFn fun t =>
                                      TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                        (inA + ↑t.divNat) (v (inA + ↑t.divNat)) t.modNat),
                                r := bobCoins,
                                received :=
                                  [Turing.pairEncode
                                      (Complexity.BinArith.encWords
                                        (List.ofFn fun i =>
                                          Complexity.BinArith.encWords
                                            (TCSlib.Cryptography.SecureComputation.garbledTable M C (seed (List.ofFn r))
                                              i)))
                                      (Turing.pairEncode
                                        (Complexity.BinArith.encWords
                                          (List.ofFn fun w =>
                                            List.ofFn
                                              (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r)) (↑w)
                                                (v ↑w))))
                                        (Complexity.BinArith.encWords
                                          (List.ofFn fun j =>
                                            Turing.pairEncode
                                              (List.ofFn
                                                (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                                  (output j) false))
                                              (List.ofFn
                                                (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                                  (output j) true)))))] }.encode
                            aliceOutput) →
                      ∀ {κ : Type u_1} [inst : Fintype κ] (D : List Bool → κ → Bool),
                        TCSlib.Cryptography.distAdv real
                            (fun r =>
                              TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C
                                (seed (List.ofFn r)) inA inB outLen output v commonInput bobInput bobCoins aliceOutput
                                0)
                            D =
                          0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.real_eq_stage0_on_tape`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.real_eq_stage0_on_tape : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2)
  (v : ℕ → Bool),
  C.size ≤ S →
    ∀
      (seed :
        List Bool →
          TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
      (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
          (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
        (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
            ((seed q).2.1 i a).1 t =
              q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
                false) →
          (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool) (t : Fin n),
              ((seed q).2.1 i a).2 t =
                q.getD
                  (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
                  false) →
            (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool)
                (t : Fin C.gates[i].args.length),
                ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
              ∀
                (M :
                  TCSlib.Cryptography.SecureComputation.MultiEnc (Fin n → Bool) (List Bool)
                    ((Fin n → Bool) × (Fin n → Bool)))
                (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (commonInput bobInput bobCoins aliceOutput : List Bool)
                (real : (Fin (10 * S * n + 2 * S) → Bool) → List Bool),
                (∀ (r : Fin (10 * S * n + 2 * S) → Bool),
                    real r =
                      Turing.pairEncode
                        { x := commonInput,
                            z :=
                              Turing.pairEncode bobInput
                                (List.ofFn fun t =>
                                  TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r)) (inA + ↑t.divNat)
                                    (v (inA + ↑t.divNat)) t.modNat),
                            r := bobCoins,
                            received :=
                              [Turing.pairEncode
                                  (Complexity.BinArith.encWords
                                    (List.ofFn fun i =>
                                      Complexity.BinArith.encWords
                                        (TCSlib.Cryptography.SecureComputation.garbledTable M C (seed (List.ofFn r))
                                          i)))
                                  (Turing.pairEncode
                                    (Complexity.BinArith.encWords
                                      (List.ofFn fun w =>
                                        List.ofFn
                                          (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r)) (↑w)
                                            (v ↑w))))
                                    (Complexity.BinArith.encWords
                                      (List.ofFn fun j =>
                                        Turing.pairEncode
                                          (List.ofFn
                                            (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                              (output j) false))
                                          (List.ofFn
                                            (TCSlib.Cryptography.SecureComputation.keyAt C (seed (List.ofFn r))
                                              (output j) true)))))] }.encode
                        aliceOutput) →
                  ∀ (r : Fin (10 * S * n + 2 * S) → Bool),
                    real r =
                      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C
                        (seed
                          (List.ofFn
                            ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel S n
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask C S v)
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm C S hA v)
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask C S v))
                              r)))
                        inA inB outLen output v commonInput bobInput bobCoins aliceOutput 0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.sample_end_of_result`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.sample_end_of_result : ∀
  {inputs width : ℕ} {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (result : Fin outLen → Bool),
  (∀ (j : Fin outLen), v (output j) = result j) →
    ∀ (commonInput bobInput bobCoins aliceOutput : List Bool),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C s inA inB outLen output v
          commonInput bobInput bobCoins aliceOutput (2 * C.gates.length) =
        Turing.pairEncode
          { x := commonInput,
              z :=
                Turing.pairEncode bobInput
                  (List.ofFn
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s inA inB)),
              r := bobCoins,
              received :=
                [TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.message M C s inA outLen output
                    result] }.encode
          aliceOutput
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex : ℕ → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex_eq : ∀ (q : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex q = (Unit ⊕ Fin (q + 1))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data : {m : ℕ} →
  BoolCircuit.DAGCircuit m → Type → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data C V =
    ((Fin C.size → Bool → V) × ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → V × V))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index : {m : ℕ} →
  BoolCircuit.DAGCircuit m → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C =
    (Fin C.size × Bool ⊕ TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.Index C)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations : {m : ℕ} →
  BoolCircuit.DAGCircuit m → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations C =
    ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv : (q : ℕ) →
  (V : Type) →
    V × (Fin (q + 1) → V) ≃ (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex q → V)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv_eq : ∀ (q : ℕ) (V : Type)
  (k : V) (r : Fin (q + 1) → V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv q V) (k, r) =
    Sum.elim (fun x => k) r
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv_symm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv_symm : ∀ (q : ℕ) (V : Type)
  (f : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex q → V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv q V).symm f =
    (f (Sum.inl ()), fun j => f (Sum.inr j))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (V : Type) →
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data C V ≃
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C → V)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type)
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data C V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv C V) d =
    Sum.elim (fun label => d.1 label.1 label.2) fun x =>
      if x.snd.2 = true then (d.2 x.fst x.snd.1).2 else (d.2 x.fst x.snd.1).1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv_fill`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv_fill : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C V (V × V)) (u : Fin C.size) (q : ℕ) (k : V)
  (r : Fin (q + 1) → V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv C V)
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r).1,
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r).2.1) =
    fun x =>
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick C rows s.2.2 u q x).elim
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv C V) (s.1, s.2.1) x)
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv q V) (k, r))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv_symm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv_symm : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type)
  (f : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C → V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv C V).symm f =
    (fun v b => f (Sum.inl (v, b)), fun i a => (f (Sum.inr ⟨i, (a, false)⟩), f (Sum.inr ⟨i, (a, true)⟩)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.paramEquiv`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.paramEquiv : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (V P : Type) →
      P × TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data C V ≃
        P × (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C → V)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.paramEquiv_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.paramEquiv_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V P : Type) (p : P)
  (d : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Data C V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.paramEquiv C V P) (p, d) =
    (p, (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv C V) d)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.paramEquiv_symm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.paramEquiv_symm : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V P : Type) (p : P)
  (f : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C → V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.paramEquiv C V P).symm (p, f) =
    (p, (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv C V).symm f)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations C →
        Fin C.size →
          (q : ℕ) →
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C →
              Option (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex q)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations C) (u : Fin C.size) (q : ℕ)
  (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick C rows perm u q x =
    Sum.elim (fun label => if label = (u, true) then some (Sum.inl ()) else none)
      (fun nonce =>
        Option.map Sum.inr
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.pick C rows perm (↑u) q nonce))
      x
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick_iff_place`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick_iff_place : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations C) (u : Fin C.size) (q : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      (∀ (i : Fin C.gates.length), (rows i).Nodup) →
        ∀ (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C)
          (j : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex q),
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick C rows perm u q x = some j ↔
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.place C rows perm u q j = some x
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.place`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.place : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations C →
        Fin C.size →
          (q : ℕ) →
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex q →
              Option (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.place_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.place_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations C) (u : Fin C.size) (q : ℕ)
  (j : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.ChallengeIndex q),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.place C rows perm u q j =
    Sum.elim (fun x => some (Sum.inl (u, true)))
      (fun nonce =>
        Option.map Sum.inr
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates.place C rows perm (↑u) q nonce))
      j
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (V : Type) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed C V (V × V) ≃
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations C ×
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C → V)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C V (V × V)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv C V) s =
    (s.2.2,
      Sum.elim (fun label => s.1 label.1 label.2) fun x =>
        if x.snd.2 = true then (s.2.1 x.fst x.snd.1).2 else (s.2.1 x.fst x.snd.1).1)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_eq_data`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_eq_data : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C V (V × V)),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv C V) s =
    (s.2.2, (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv C V) (s.1, s.2.1))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_fill`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_fill : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C V (V × V)) (u : Fin C.size) (q : ℕ) (k : V)
  (r : Fin (q + 1) → V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv C V)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r) =
    (s.2.2, fun x =>
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.pick C rows s.2.2 u q x).elim
        ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.dataEquiv C V) (s.1, s.2.1) x)
        ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.challengeEquiv q V) (k, r)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_key : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C V (V × V))
  (v : Fin C.size) (b : Bool),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv C V) s).2 (Sum.inl (v, b)) = s.1 v b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_nonce`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_nonce : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C V (V × V))
  (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (half : Bool),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv C V) s).2 (Sum.inr ⟨i, (a, half)⟩) =
    if half = true then (s.2.1 i a).2 else (s.2.1 i a).1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_perm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_perm : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C V (V × V)),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv C V) s).1 = s.2.2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_symm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv_symm : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (V : Type)
  (p : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Permutations C)
  (f : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.Index C → V),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates.seedEquiv C V).symm (p, f) =
    (fun v b => f (Sum.inl (v, b)), fun i a => (f (Sum.inr ⟨i, (a, false)⟩), f (Sum.inr ⟨i, (a, true)⟩)), p)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_budget`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_budget : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u).length ≤
          q + 1 →
        (∀ (i : Fin C.gates.length), (rows i).length ≤ 4) →
          ∀ (tail privateInput aliceOutput : List Bool) (S Q T I A : Complexity.PolyExpr),
            C.gates.length ≤ S.eval n →
              q ≤ Q.eval n →
                tail.length ≤ T.eval n →
                  privateInput.length ≤ I.eval n →
                    aliceOutput.length ≤ A.eval n →
                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice
                            (Complexity.BinArith.encWords
                              (List.map Complexity.BinArith.encWords
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁
                                  E₂ o)))
                            tail privateInput aliceOutput).length ≤
                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget S Q T I
                              A).eval
                          n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_budget._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_budget._proof_1_1 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (tail privateInput aliceOutput : List Bool) (S Q T I A : Complexity.PolyExpr),
  q ≤ Q.eval n → ¬2 * q + 7 * n + 8 ≤ 2 * Q.eval n + 7 * n + 8 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_budget._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_budget._proof_1_2 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (tail privateInput aliceOutput : List Bool) (S Q T I A : Complexity.PolyExpr),
  2 * q + 7 * n + 8 ≤ 2 * Q.eval n + 7 * n + 8 →
    ¬16 * (2 * q + 7 * n + 8) + 18 ≤ 16 * (2 * Q.eval n + 7 * n + 8) + 18 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_budget._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_budget._proof_1_3 : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool)
  (tail privateInput aliceOutput : List Bool) (S Q T I A : Complexity.PolyExpr),
  tail.length ≤ T.eval n →
    privateInput.length ≤ I.eval n →
      aliceOutput.length ≤ A.eval n →
        C.gates.length * (16 * (2 * q + 7 * n + 8) + 18) ≤ S.eval n * (16 * (2 * Q.eval n + 7 * n + 8) + 18) →
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice
                  (Complexity.BinArith.encWords
                    (List.map Complexity.BinArith.encWords
                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂ o)))
                  tail privateInput aliceOutput).length ≤
              2 * (C.gates.length * (16 * (2 * q + 7 * n + 8) + 18)) + 2 * tail.length + 2 * privateInput.length +
                  aliceOutput.length +
                6 →
            ¬(TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice
                      (Complexity.BinArith.encWords
                        (List.map Complexity.BinArith.encWords
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂
                            o)))
                      tail privateInput aliceOutput).length ≤
                  2 * (S.eval n * (16 * (2 * Q.eval n + 7 * n + 8) + 18)) + 2 * T.eval n + 2 * I.eval n + A.eval n + 6 →
              False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_le : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u).length ≤
          q + 1 →
        (∀ (i : Fin C.gates.length), (rows i).length ≤ 4) →
          ∀ (tail privateInput aliceOutput : List Bool),
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice
                  (Complexity.BinArith.encWords
                    (List.map Complexity.BinArith.encWords
                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂ o)))
                  tail privateInput aliceOutput).length ≤
              2 * C.gates.length * (16 * (2 * q + 7 * n + 8) + 18) + 2 * tail.length + 2 * privateInput.length +
                  aliceOutput.length +
                6
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.advice_le._proof_1_1 : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool)
  (tail privateInput aliceOutput : List Bool),
  2 *
        (Complexity.BinArith.encWords
            (List.map Complexity.BinArith.encWords
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂ o))).length ≤
      2 * (C.gates.length * (16 * (2 * q + 7 * n + 8) + 18)) →
    ¬2 *
                    (Complexity.BinArith.encWords
                        (List.map Complexity.BinArith.encWords
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂
                            o))).length +
                  2 * tail.length +
                2 * privateInput.length +
              aliceOutput.length +
            6 ≤
          2 * (C.gates.length * (16 * (2 * q + 7 * n + 8) + 18)) + 2 * tail.length + 2 * privateInput.length +
              aliceOutput.length +
            6 →
      False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget : Complexity.PolyExpr →
  Complexity.PolyExpr → Complexity.PolyExpr → Complexity.PolyExpr → Complexity.PolyExpr → Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget_eq : ∀
  (S Q T I A : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget S Q T I A =
    have row :=
      (((Complexity.PolyExpr.const 2).mul Q).add ((Complexity.PolyExpr.const 7).mul Complexity.PolyExpr.var)).add
        (Complexity.PolyExpr.const 8);
    have descriptors :=
      ((Complexity.PolyExpr.const 2).mul S).mul
        (((Complexity.PolyExpr.const 16).mul row).add (Complexity.PolyExpr.const 18));
    (((descriptors.add ((Complexity.PolyExpr.const 2).mul T)).add ((Complexity.PolyExpr.const 2).mul I)).add A).add
      (Complexity.PolyExpr.const 6)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget_eval`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget_eval : ∀
  (S Q T I A : Complexity.PolyExpr) (n : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget S Q T I A).eval n =
    2 * S.eval n * (16 * (2 * Q.eval n + 7 * n + 8) + 18) + 2 * T.eval n + 2 * I.eval n + A.eval n + 6
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.encodedTables_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.encodedTables_le : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u).length ≤
          q + 1 →
        (∀ (i : Fin C.gates.length), (rows i).length ≤ 4) →
          (Complexity.BinArith.encWords
                (List.map Complexity.BinArith.encWords
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂
                    o))).length ≤
            C.gates.length * (16 * (2 * q + 7 * n + 8) + 18)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.encodedTables_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.encodedTables_le._proof_1_1 : ∀
  {m n : ℕ} (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  ¬2 * (4 * (2 * (2 * q + 7 * n + 8) + 2)) + 2 = 16 * (2 * q + 7 * n + 8) + 18 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.messageTail_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.messageTail_le : ∀ {m n : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin n → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit m) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ρ)
  (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ),
  (Complexity.pairSndD
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v
          stage)).length ≤
    2 * (inA * (2 * n + 2)) + 2 + outLen * (6 * n + 6)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget : Complexity.PolyExpr →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget_eq : ∀
  (B : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget B =
    (((Complexity.PolyExpr.const 2).mul B).add (Complexity.PolyExpr.const 2)).add (B.mul Complexity.PolyExpr.var)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget_eval`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget_eval : ∀
  (B : Complexity.PolyExpr) (n : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget B).eval n =
    2 * B.eval n + 2 + B.eval n * n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateInput_length`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateInput_length : ∀ {m n : ℕ}
  {ρ : Type} (C : BoolCircuit.DAGCircuit m) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ρ)
  (first count : ℕ) (bobInput : List Bool),
  (Turing.pairEncode bobInput
        (List.ofFn
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s first count))).length =
    2 * bobInput.length + 2 + count * n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u).length ≤
          q + 1 →
        ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record C rows s u E₁ E₂ o i a).length ≤
            2 * q + 7 * n + 8
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_1_1 : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u).length ≤ q + 1 →
    ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      ((TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc
              (TCSlib.Cryptography.SecureComputation.argKeys C s i a) (o i a) (s.2.1 i a)).length ≤
          7 * n + 4 →
        ¬((TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc
                    (TCSlib.Cryptography.SecureComputation.argKeys C s i a) (o i a) (s.2.1 i a)).length +
                2 ≤
              2 * q + 7 * n + 8 →
          False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_1_2 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool)
  (p : Fin C.gates[↑i].args.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows s.2.2 (↑u) i a p < q + 1 →
    ¬TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows s.2.2 (↑u) i a p ≤ q → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_1_3 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool)
  (p : Fin C.gates[↑i].args.length), ¬2 * q + 3 * n + 8 ≤ 2 * q + 7 * n + 8 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.record_le._proof_2 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sampleBudget`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sampleBudget : Complexity.PolyExpr →
  Complexity.PolyExpr → Complexity.PolyExpr → Complexity.PolyExpr → Complexity.PolyExpr → Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sampleBudget_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sampleBudget_eq : ∀
  (S A B O R : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sampleBudget S A B O R =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.budget S
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget A O)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.privateBudget B) R
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool)
  (S A B O R : Complexity.PolyExpr) (output : Fin (O.eval n) → ℕ) (v : ℕ → Bool) (stage : ℕ)
  (bobInput aliceOutput : List Bool),
  C.IsFaninTwo →
    C.size ≤ S.eval n →
      (∀ (i : Fin C.gates.length), rows i = Finset.univ.toList) →
        bobInput.length ≤ B.eval n →
          aliceOutput.length ≤ R.eval n →
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice C rows s u E₁ E₂ o
                  (Complexity.pairSndD
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message
                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C s (A.eval n) (O.eval n) output v
                      stage))
                  (Turing.pairEncode bobInput
                    (List.ofFn
                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s (A.eval n)
                        (B.eval n))))
                  aliceOutput).length ≤
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sampleBudget S A B O R).eval n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1 : ∀
  {m : ℕ} {n : ℕ} (C : BoolCircuit.DAGCircuit m) (S : Complexity.PolyExpr), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1_1 : ∀
  {m : ℕ} {n : ℕ} (C : BoolCircuit.DAGCircuit m) (S B R : Complexity.PolyExpr) (bobInput aliceOutput : List Bool),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1_2 : ∀
  {m n : ℕ} (C : BoolCircuit.DAGCircuit m) (S B R : Complexity.PolyExpr) (bobInput aliceOutput : List Bool),
  m + C.gates.length ≤ S.eval n → ¬C.gates.length ≤ S.eval n → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1_3 : ∀
  {m n : ℕ} (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (S B R : Complexity.PolyExpr) (bobInput aliceOutput : List Bool),
  C.gates.length ≤ S.eval n →
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u).length ≤
        4 * C.gates.length →
      ¬(TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u).length ≤
            4 * S.eval n + 1 →
        False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sample_advice_budget._proof_1_4 : ∀
  {m n : ℕ} (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (S A B O R : Complexity.PolyExpr) (output : Fin (O.eval n) → ℕ) (v : ℕ → Bool) (stage : ℕ)
  (bobInput aliceOutput : List Bool),
  bobInput.length ≤ B.eval n → ¬2 * bobInput.length + 2 + B.eval n * n ≤ 2 * B.eval n + 2 + B.eval n * n → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget : Complexity.PolyExpr →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget_eq : ∀
  (S : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S =
    (Complexity.PolyExpr.const 4).mul S
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget_eval`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget_eval : ∀
  (S : Complexity.PolyExpr) (n : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n = 4 * S.eval n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.table_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.table_le : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u).length ≤
          q + 1 →
        (∀ (i : Fin C.gates.length), (rows i).length ≤ 4) →
          ∀ (i : Fin C.gates.length),
            (Complexity.BinArith.encWords
                  (List.map
                    (fun a =>
                      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record C rows s u E₁ E₂ o i
                        ((s.2.2 i) a))
                    (rows i))).length ≤
              4 * (2 * (2 * q + 7 * n + 8) + 2)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget : Complexity.PolyExpr →
  Complexity.PolyExpr → Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget_eq : ∀
  (A O : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget A O =
    (((Complexity.PolyExpr.const 2).mul
              (A.mul
                (((Complexity.PolyExpr.const 2).mul Complexity.PolyExpr.var).add (Complexity.PolyExpr.const 2)))).add
          (Complexity.PolyExpr.const 2)).add
      (O.mul (((Complexity.PolyExpr.const 6).mul Complexity.PolyExpr.var).add (Complexity.PolyExpr.const 6)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget_eval`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget_eval : ∀
  (A O : Complexity.PolyExpr) (n : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.tailBudget A O).eval n =
    2 * (A.eval n * (2 * n + 2)) + 2 + O.eval n * (6 * n + 6)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.activeAnswers_fill`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.activeAnswers_fill : ∀ {inputs width : ℕ}
  {ρ : Type} (C : BoolCircuit.DAGCircuit inputs)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) (ρ × ρ)) (u : Fin C.size) (q : ℕ)
  (k : Fin width → Bool) (rs : Fin (q + 1) → ρ) (first count : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs) first count =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s first count
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.decodePair_fill`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.decodePair_fill : ∀ {inputs : ℕ}
  {K ρ : Type} [inst : Inhabited K] (C : BoolCircuit.DAGCircuit inputs)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (rs : Fin (q + 1) → ρ) (w : ℕ) (b : Bool),
  w ≠ ↑u →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair C
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs) w b =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.decodePair C s w b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_false`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_false : ∀ {inputs : ℕ} {K ρ : Type}
  [inst : Inhabited K] (C : BoolCircuit.DAGCircuit inputs)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (rs : Fin (q + 1) → ρ) (w : ℕ),
  TCSlib.Cryptography.SecureComputation.keyAt C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs) w false =
    TCSlib.Cryptography.SecureComputation.keyAt C s w false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_of_label_ne`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_of_label_ne : ∀ {inputs : ℕ}
  {K ρ : Type} [inst : Inhabited K] (C : BoolCircuit.DAGCircuit inputs)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (rs : Fin (q + 1) → ρ) (w : ℕ) (b : Bool),
  (w, b) ≠ (↑u, true) →
    TCSlib.Cryptography.SecureComputation.keyAt C
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs) w b =
      TCSlib.Cryptography.SecureComputation.keyAt C s w b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_of_ne`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_of_ne : ∀ {inputs : ℕ} {K ρ : Type}
  [inst : Inhabited K] (C : BoolCircuit.DAGCircuit inputs)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (rs : Fin (q + 1) → ρ) (w : ℕ) (b : Bool),
  w ≠ ↑u →
    TCSlib.Cryptography.SecureComputation.keyAt C
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs) w b =
      TCSlib.Cryptography.SecureComputation.keyAt C s w b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_eq_of_stageBit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_eq_of_stageBit_eq : ∀
  {inputs width : ℕ} {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage stage' : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v stage =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v stage' →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v stage =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v stage'
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_tail_fill`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_tail_fill : ∀ {inputs width : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) (ρ × ρ))
  (C : BoolCircuit.DAGCircuit inputs) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) (ρ × ρ)) (u : Fin C.size) (q : ℕ)
  (k : Fin width → Bool) (rs : Fin (q + 1) → ρ) (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ),
  (∀ (j : Fin outLen), output j ≠ ↑u) →
    Complexity.pairSndD
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs) inA outLen output v
          stage) =
      Complexity.pairSndD
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v stage)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_tail_stage_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_tail_stage_eq : ∀ {inputs width : ℕ}
  {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage stage' : ℕ),
  Complexity.pairSndD
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v stage) =
    Complexity.pairSndD
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message M C s inA outLen output v stage')
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i₀ : Fin C.gates.length) (phase u : ℕ),
  u ∈ C.gates[↑i₀].args →
    ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      (inputs + ↑i, TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v (↑i₀) phase i a) ≠
        (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne_of_lt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne_of_lt : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase u : ℕ),
  u < inputs + cutoff →
    ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      (inputs + ↑i, TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit C v cutoff phase i a) ≠
        (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne_of_lt._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne_of_lt._proof_1 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (cutoff u : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.sample_eq_of_stageBit_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.sample_eq_of_stageBit_eq : ∀
  {inputs width : ℕ} {ρ : Type} (M : TCSlib.Cryptography.SecureComputation.MultiEnc (Fin width → Bool) (List Bool) ρ)
  (C : BoolCircuit.DAGCircuit inputs) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin width → Bool) ρ)
  (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (commonInput bobInput bobCoins aliceOutput : List Bool)
  (stage stage' : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v stage =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v stage' →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C s inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput stage =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample M C s inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput stage'
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_bit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_bit : ∀
  (g : BoolCircuit.DAGGate) (a : Fin g.args.length → Bool) (u : ℕ),
  g.args.Nodup →
    ∀ (p : Fin g.args.length),
      g.args[↑p] = u →
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition g a u = none → a p = false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_bit._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_bit._proof_1 : ∀
  (g : BoolCircuit.DAGGate), ¬g.args.length ≤ g.args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_getD`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_getD : ∀
  (g : BoolCircuit.DAGGate) (a : Fin g.args.length → Bool) (u : ℕ),
  g.args.Nodup →
    ∀ (p : Fin g.args.length),
      g.args[↑p] = u →
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition g a u = none →
          (List.ofFn a).getD (↑p) false = false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_even`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_even : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i₀ : Fin C.gates.length),
  ∀ u ∈ C.gates[↑i₀].args,
    ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      (inputs + ↑i, TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀) i a) ≠
        (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_next`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_next : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i₀ : Fin C.gates.length),
  ∀ u ∈ C.gates[↑i₀].args,
    ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      (inputs + ↑i, TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + 2) i a) ≠
        (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_next._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_next._proof_1_1 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i₀ : Fin C.gates.length),
  ∀ u < inputs + ↑i₀, ¬u < inputs + (↑i₀ + 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_next._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_next._proof_1_2 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i₀ : Fin C.gates.length) (u : ℕ),
  ¬2 * ↑i₀ + 2 = 2 * (↑i₀ + 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_odd`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_odd : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i₀ : Fin C.gates.length),
  ∀ u ∈ C.gates[↑i₀].args,
    ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      (inputs + ↑i, TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + 1) i a) ≠
        (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_of_arity_zero`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_of_arity_zero : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i₀ : Fin C.gates.length),
  C.gates[↑i₀].args.length = 0 →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀) =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + 1)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool) (i₀ : Fin C.gates.length),
  C.gates[↑i₀].args.Nodup →
    ∀ (p : Fin C.gates[↑i₀].args.length),
      ↑p = 0 →
        ∀ (u : ℕ),
          C.gates[↑i₀].args[↑p] = u →
            ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
              TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a u =
                  none →
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀) i a =
                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + 1) i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected._proof_1 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected._proof_2 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length),
  ¬C.gates[↑i₀].args.length ≤ C.gates[↑i₀].args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected._proof_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected._proof_3 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length) (u : ℕ),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_of_arity_le_one`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_of_arity_le_one : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    (∀ (i : Fin C.gates.length),
        TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
          v (inputs + ↑i)) →
      ∀ (i₀ : Fin C.gates.length),
        C.gates[↑i₀].args.length ≤ 1 →
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + 1) =
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + 2)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_of_arity_le_one._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_of_arity_le_one._proof_1_1 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i₀ : Fin C.gates.length), ¬2 * ↑i₀ + 2 = 2 * (↑i₀ + 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_unselected`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_unselected : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (v : ℕ → Bool),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    (∀ (i : Fin C.gates.length),
        TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
          v (inputs + ↑i)) →
      ∀ (i₀ : Fin C.gates.length),
        C.gates[↑i₀].args.Nodup →
          ∀ (p : Fin C.gates[↑i₀].args.length),
            ↑p = 1 →
              ∀ (u : ℕ),
                C.gates[↑i₀].args[↑p] = u →
                  ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a
                          u =
                        none →
                      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + 1) i a =
                        TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + 2) i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_unselected._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_unselected._proof_1_1 : ∀
  {inputs : ℕ} (C : BoolCircuit.DAGCircuit inputs) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length) (u : ℕ),
  ¬2 * ↑i₀ + 2 = 2 * (↑i₀ + 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedLaw.acceptProb_fill`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedLaw.acceptProb_fill : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
    C.size ≤ S →
      ∀
        (seed :
          List Bool →
            TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
        (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
            (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
          (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (t : Fin n),
              ((seed q).2.1 i a).1 t =
                q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
                  false) →
            (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (t : Fin n),
                ((seed q).2.1 i a).2 t =
                  q.getD
                    (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
                    false) →
              (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool)
                  (t : Fin C.gates[↑i].args.length),
                  ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
                ∀ (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) (u : Fin C.size)
                  (q : ℕ),
                  (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
                    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
                      (∀ (i : Fin C.gates.length), (rows i).Nodup) →
                        ∀ {γ : Type u_1} {κ : Type u_2} [inst : Fintype κ]
                          (X :
                            TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool)
                                ((Fin n → Bool) × (Fin n → Bool)) →
                              γ)
                          (D : γ → κ → Bool),
                          TCSlib.Cryptography.acceptProb
                              (fun z =>
                                X
                                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows
                                    (seed (List.ofFn z.1)) u q z.2.1 z.2.2))
                              D =
                            TCSlib.Cryptography.acceptProb (fun r => X (seed (List.ofFn r))) D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice : {m n : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) →
        Fin C.size →
          (List Bool → List Bool) →
            (List Bool → List Bool) →
              ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) →
                List Bool → List Bool → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice_congr`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice_congr : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (E₁ E₂ : List Bool → List Bool)
  (o₀ o₁ : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a ↑u = none →
        o₀ i a = o₁ i a) →
    ∀ (tail privateInput aliceOutput : List Bool),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice C rows s u E₁ E₂ o₀ tail privateInput
          aliceOutput =
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice C rows s u E₁ E₂ o₁ tail privateInput
          aliceOutput
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice_eq : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (E₁ E₂ : List Bool → List Bool)
  (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool)
  (tail privateInput aliceOutput : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice C rows s u E₁ E₂ o tail privateInput
      aliceOutput =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice
      (Complexity.BinArith.encWords
        (List.map Complexity.BinArith.encWords
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂ o)))
      tail privateInput aliceOutput
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record : {m n : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) →
        Fin C.size →
          (List Bool → List Bool) →
            (List Bool → List Bool) →
              ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) →
                (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record_congr`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record_congr : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (E₁ E₂ : List Bool → List Bool)
  (o₀ o₁ : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a ↑u = none →
      o₀ i a = o₁ i a) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record C rows s u E₁ E₂ o₀ i a =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record C rows s u E₁ E₂ o₁ i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record_eq : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (E₁ E₂ : List Bool → List Bool)
  (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record C rows s u E₁ E₂ o i a =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a ↑u).elim
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.fixedRecord
        ((TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc
          (TCSlib.Cryptography.SecureComputation.argKeys C s i a) (o i a) (s.2.1 i a)))
      fun p =>
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor n
        (TCSlib.Cryptography.SecureComputation.argKeys C s i a) (s.2.1 i a) (↑p)
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows s.2.2 (↑u) i a p)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength : {m n : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) →
        Fin C.size → (q : ℕ) → Fin (q + 1) → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength_eq : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u q j =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u) j).elim
      n fun t =>
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length n
        (TCSlib.Cryptography.SecureComputation.argKeys C s t.1 ((s.2.2 t.1) ((rows t.1).getD t.2.1 fun x => false)))
        t.2.2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage : {m n : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))) →
        (u : Fin C.size) →
          (q : ℕ) →
            (List Bool → List Bool) →
              ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) →
                (j : Fin (q + 1)) →
                  Fin (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u q j) →
                    Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage_eq : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (E₁ : List Bool → List Bool)
  (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage C rows s u q E₁ o j =
    TCSlib.Cryptography.padFin
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u q j)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord C rows s u q E₁ o j)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage_ofFn`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage_ofFn : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) {G₁ : (k : ℕ) → (Fin k → Bool) → (Fin k → Bool) → Fin (k + k) → Bool}
  {E₁ : List Bool → List Bool},
  (∀ (k : ℕ) (key nonce : Fin k → Bool),
      E₁ (Turing.pairEncode (List.ofFn key) (List.ofFn nonce)) = List.ofFn (G₁ k key nonce)) →
    ∀ (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) (j : Fin (q + 1)),
      List.ofFn (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage C rows s u q E₁ o j) =
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord C rows s u q E₁ o j
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset : {m n : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) →
        Fin C.size → (q : ℕ) → Fin (q + 1) → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (t : Fin C.gates.length × ℕ × ℕ), ↑t.1 < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset_eq : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C rows s u q j =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u) j).elim
      0 fun t =>
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset n
        (TCSlib.Cryptography.SecureComputation.argKeys C s t.1 ((s.2.2 t.1) ((rows t.1).getD t.2.1 fun x => false)))
        t.2.2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotReaders_of_padded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotReaders_of_padded : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (E₁ : List Bool → List Bool)
  (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) (j : Fin (q + 1))
  (i : Fin C.gates.length) (row p : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u) j =
      some (i, row, p) →
    have a := (s.2.2 i) ((rows i).getD row fun x => false);
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C rows s u q j =
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset n
          (TCSlib.Cryptography.SecureComputation.argKeys C s i a) p ∧
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u q j =
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length n
            (TCSlib.Cryptography.SecureComputation.argKeys C s i a) p ∧
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord C rows s u q E₁ o j =
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word E₁ n
            (TCSlib.Cryptography.SecureComputation.argKeys C s i a) (o i a) (s.2.1 i a) p
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord : {m n : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) →
        Fin C.size →
          (q : ℕ) →
            (List Bool → List Bool) →
              ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) → Fin (q + 1) → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord_eq : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (E₁ : List Bool → List Bool)
  (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord C rows s u q E₁ o j =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2 ↑u) j).elim
      (List.replicate n false) fun t =>
      have a := (s.2.2 t.1) ((rows t.1).getD t.2.1 fun x => false);
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word E₁ n
        (TCSlib.Cryptography.SecureComputation.argKeys C s t.1 a) (o t.1 a) (s.2.1 t.1 a) t.2.2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord_length`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord_length : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) {G₁ : (k : ℕ) → (Fin k → Bool) → (Fin k → Bool) → Fin (k + k) → Bool}
  {E₁ : List Bool → List Bool},
  (∀ (k : ℕ) (key nonce : Fin k → Bool),
      E₁ (Turing.pairEncode (List.ofFn key) (List.ofFn nonce)) = List.ofFn (G₁ k key nonce)) →
    ∀ (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) (j : Fin (q + 1)),
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotWord C rows s u q E₁ o j).length =
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u q j
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slots_fit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slots_fit : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C rows s u q j + n +
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u q j ≤
    n + n + (n + (4 * n + 2))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables : {m n : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) →
        Fin C.size →
          (List Bool → List Bool) →
            (List Bool → List Bool) →
              ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool) → List (List (List Bool))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables_congr`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables_congr : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (E₁ E₂ : List Bool → List Bool)
  (o₀ o₁ : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a ↑u = none →
        o₀ i a = o₁ i a) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂ o₀ =
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂ o₁
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables_eq : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (E₁ E₂ : List Bool → List Bool)
  (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂ o =
    List.ofFn fun i =>
      List.map
        (fun a =>
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record C rows s u E₁ E₂ o i ((s.2.2 i) a))
        (rows i)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor : (n : ℕ) →
  List (Fin n → Bool) → (Fin n → Bool) × (Fin n → Bool) → ℕ → ℕ → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor_eq : ∀ (n : ℕ)
  (ks : List (Fin n → Bool)) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p j : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor n ks nonce p j =
    if ks.length = 2 ∧ p = 1 then
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord j
        (List.ofFn (ks.getD 0 default)) (List.ofFn nonce.1)
    else TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord j
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor_length_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor_length_le : ∀ (n q : ℕ)
  (ks : List (Fin n → Bool)) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p j : ℕ),
  j ≤ q →
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor n ks nonce p j).length ≤
      2 * q + 3 * n + 8
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor_length_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor_length_le._proof_1_1 : ∀ (n q : ℕ)
  (ks : List (Fin n → Bool)) (p j : ℕ), j ≤ q → ¬2 * j + 2 * n + n + 8 ≤ 2 * q + 3 * n + 8 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor_length_le._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor_length_le._proof_1_2 : ∀
  (n q j : ℕ), j ≤ q → ¬2 * j + 6 ≤ 2 * q + 3 * n + 8 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.fits`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.fits : ∀ (n : ℕ) (ks : List (Fin n → Bool))
  (p : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset n ks p + n +
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length n ks p ≤
    n + n + (n + (4 * n + 2))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length : (n : ℕ) → List (Fin n → Bool) → ℕ → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length_eq : ∀ (n : ℕ)
  (ks : List (Fin n → Bool)) (p : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length n ks p =
    if ks.length = 2 ∧ p = 0 then 4 * n + 2 else n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.message`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.message : (List Bool → List Bool) →
  (n : ℕ) →
    (ks : List (Fin n → Bool)) →
      (Fin n → Bool) →
        (Fin n → Bool) × (Fin n → Bool) →
          (p : ℕ) → Fin (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length n ks p) → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.message_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.message_eq : ∀ (E₁ : List Bool → List Bool)
  (n : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.message E₁ n ks o nonce p =
    TCSlib.Cryptography.padFin (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length n ks p)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word E₁ n ks o nonce p)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.message_ofFn`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.message_ofFn : ∀
  {G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool} {E₁ : List Bool → List Bool},
  (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
    ∀ (n : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ),
      List.ofFn (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.message E₁ n ks o nonce p) =
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word E₁ n ks o nonce p
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset : (n : ℕ) → List (Fin n → Bool) → ℕ → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset_eq : ∀ (n : ℕ)
  (ks : List (Fin n → Bool)) (p : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset n ks p =
    if ks.length = 2 ∧ p = 0 then n + n else 0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
        ∀ (n q : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ)
          (j : Fin (q + 1)),
          ks.length ≤ 2 →
            p < ks.length →
              ∀ (offsets lens : Fin (q + 1) → ℕ) (msgs : (i : Fin (q + 1)) → Fin (lens i) → Bool),
                offsets j = TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.offset n ks p →
                  List.ofFn (msgs j) =
                      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word E₁ n ks o nonce p →
                    ∀ (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool),
                      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
                          (Turing.pairEncode
                            (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q offsets lens msgs (k, rs))
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.descriptor n ks nonce p
                              ↑j)) =
                        (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc (ks.set p k) o
                          (if p = 0 then (rs j, nonce.2) else (nonce.1, rs j))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_1 : ∀ (n p : ℕ),
  p < 0 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_2 : ∀ (n q p : ℕ)
  (j : Fin (q + 1)) (offsets : Fin (q + 1) → ℕ) (k₀ : Fin n → Bool), p < 0 + 1 → ¬p = 0 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_3 : ∀ (n q : ℕ)
  (j : Fin (q + 1)) (offsets : Fin (q + 1) → ℕ) (k₀ : Fin n → Bool), 0 + 1 = 2 ∧ 0 = 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_4 : ∀ (n q : ℕ)
  (j : Fin (q + 1)) (offsets : Fin (q + 1) → ℕ) (k₀ : Fin n → Bool), 0 + 1 = 2 ∧ True → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_5`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_5 : ∀ (n q p : ℕ)
  (j : Fin (q + 1)) (offsets : Fin (q + 1) → ℕ) (k₀ k₁ : Fin n → Bool) (tail : List (Fin n → Bool)),
  tail.length + 1 + 1 ≤ 2 → ¬tail.length = 0 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_6`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_6 : ∀ (n q p : ℕ)
  (j : Fin (q + 1)) (offsets : Fin (q + 1) → ℕ) (k₀ k₁ : Fin n → Bool), p < 0 + 1 + 1 → ¬(p = 0 ∨ p = 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_7`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_7 : ∀ (n q : ℕ)
  (j : Fin (q + 1)) (offsets : Fin (q + 1) → ℕ) (k₀ k₁ : Fin n → Bool), True ∧ 0 = 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_8`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.reconstruct._proof_1_8 : ∀ (n q : ℕ)
  (j : Fin (q + 1)) (offsets : Fin (q + 1) → ℕ) (k₀ k₁ : Fin n → Bool), True ∧ 1 = 0 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word : (List Bool → List Bool) →
  (n : ℕ) → List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) × (Fin n → Bool) → ℕ → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word_eq : ∀ (E₁ : List Bool → List Bool)
  (n : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word E₁ n ks o nonce p =
    if ks.length = 2 ∧ p = 0 then
      TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn (ks.getD 1 default)) (List.ofFn o)
        (List.ofFn nonce.2)
    else List.ofFn o
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word_length`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word_length : ∀
  {G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool} {E₁ : List Bool → List Bool},
  (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
    ∀ (n : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ),
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.word E₁ n ks o nonce p).length =
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows.length n ks p
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.argument_label_eq_iff`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.argument_label_eq_iff : ∀
  (g : BoolCircuit.DAGGate) (a : Fin g.args.length → Bool) (u : ℕ),
  g.args.Nodup →
    ∀ (p : Fin g.args.length),
      g.args[↑p] = u → a p = true → ∀ (t : Fin g.args.length), (g.args[↑t], a t) = (u, true) ↔ t = p
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.argument_label_eq_iff._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.argument_label_eq_iff._proof_1 : ∀
  (g : BoolCircuit.DAGGate), ¬g.args.length ≤ g.args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.argument_label_eq_iff._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.argument_label_eq_iff._proof_2 : ∀
  (g : BoolCircuit.DAGGate) (u : ℕ) (p : Fin g.args.length), ¬g.args.length ≤ g.args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill : {m : ℕ} →
  {K ρ : Type} →
    (C : BoolCircuit.DAGCircuit m) →
      ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
        TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ) →
          Fin C.size → (q : ℕ) → K → (Fin (q + 1) → ρ) → TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys : ∀ {m : ℕ} {K ρ : Type}
  [inst : Inhabited K] (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.argKeys C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r) i a =
    List.ofFn fun p =>
      if (C.gates[↑i].args[↑p], a p) = (↑u, true) then k
      else TCSlib.Cryptography.SecureComputation.keyAt C s C.gates[↑i].args[↑p] (a p)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys_none`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys_none : ∀ {m : ℕ} {K ρ : Type}
  [inst : Inhabited K] (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
  C.gates[↑i].args.Nodup →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a ↑u = none →
      TCSlib.Cryptography.SecureComputation.argKeys C
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r) i a =
        TCSlib.Cryptography.SecureComputation.argKeys C s i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys_some`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys_some : ∀ {m : ℕ} {K ρ : Type}
  [inst : Inhabited K] (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool)
  (p : Fin C.gates[↑i].args.length),
  C.gates[↑i].args.Nodup →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a ↑u = some p →
      TCSlib.Cryptography.SecureComputation.argKeys C
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r) i a =
        (TCSlib.Cryptography.SecureComputation.argKeys C s i a).set (↑p) k
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys_some._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys_some._proof_1_1 : ∀ {m : ℕ}
  {K ρ : Type} [Inhabited K] (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (k : K) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool) (p : Fin C.gates[↑i].args.length) (j : ℕ),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys_some._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_argKeys_some._proof_1_2 : ∀ {m : ℕ}
  {K ρ : Type} [Inhabited K] (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (k : K) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool) (p : Fin C.gates[↑i].args.length) (j : ℕ), ¬↑i < C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_eq : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r =
    (fun v b => if v = u ∧ b = true then k else s.1 v b,
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce C rows s (↑u) q r, s.2.2)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_key : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ) (v : Fin C.size) (b : Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r).1 v b =
    if v = u ∧ b = true then k else s.1 v b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_keyAt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_keyAt : ∀ {m : ℕ} {K ρ : Type}
  [inst : Inhabited K] (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ) (v : ℕ) (b : Bool),
  TCSlib.Cryptography.SecureComputation.keyAt C
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r) v b =
    if (v, b) = (↑u, true) then k else TCSlib.Cryptography.SecureComputation.keyAt C s v b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_key_other`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_key_other : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ) (v : Fin C.size) (b : Bool),
  (v, b) ≠ (u, true) →
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r).1 v b = s.1 v b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_key_selected`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_key_selected : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r).1 u true = k
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_nonce`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_nonce : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r).2.1 i a =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce C rows s (↑u) q r i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_perm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill_perm : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (r : Fin (q + 1) → ρ) (i : Fin C.gates.length),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k r).2.2 i = s.2.2 i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce : {m : ℕ} →
  {K ρ : Type} →
    (C : BoolCircuit.DAGCircuit m) →
      ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
        TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ) →
          ℕ → (q : ℕ) → (Fin (q + 1) → ρ) → (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → ρ × ρ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce_eq : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u q : ℕ) (r : Fin (q + 1) → ρ)
  (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce C rows s u q r i a =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a u).elim
      (s.2.1 i a) fun p =>
      have j := TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows s.2.2 u i a p;
      if h : j < q + 1 then if ↑p = 0 then (r ⟨j, h⟩, (s.2.1 i a).2) else ((s.2.1 i a).1, r ⟨j, h⟩) else s.2.1 i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce_of_none`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce_of_none : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u q : ℕ) (r : Fin (q + 1) → ρ)
  (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a u = none →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce C rows s u q r i a = s.2.1 i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce_of_some`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce_of_some : ∀ {m : ℕ} {K ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K (ρ × ρ)) (u q : ℕ) (r : Fin (q + 1) → ρ)
  (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (p : Fin C.gates[↑i].args.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a u = some p →
    ∀
      (hslot :
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows s.2.2 u i a p < q + 1),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.nonce C rows s u q r i a =
        if ↑p = 0 then
          (r ⟨TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows s.2.2 u i a p, hslot⟩,
            (s.2.1 i a).2)
        else
          ((s.2.1 i a).1,
            r ⟨TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows s.2.2 u i a p, hslot⟩)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) →
        (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex_actual`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex_actual : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool),
  (∀ (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
    (perm i)
        ((rows i).getD (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex C rows perm i a)
          fun x => false) =
      a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex C rows perm i a =
    List.idxOf ((Equiv.symm (perm i)) a) (rows i)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex_lt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex_lt : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool),
  (∀ (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex C rows perm i a < (rows i).length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex_of_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex_of_row : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (i : Fin C.gates.length),
  ∀ r < (rows i).length,
    (rows i).Nodup →
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex C rows perm i
          ((perm i) ((rows i).getD r fun x => false)) =
        r
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    ((i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)) →
      ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) →
        ℕ → (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin C.gates[↑i].args.length → ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool) (p : Fin C.gates[↑i].args.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows perm u i a p =
    List.idxOf (i, TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex C rows perm i a, ↑p)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_lt`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_lt : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool) (p : Fin C.gates[↑i].args.length),
  C.gates[↑i].args.Nodup →
    (∀ (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      C.gates[↑i].args[↑p] = u →
        a p = true →
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows perm u i a p <
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u).length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_lt._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_lt._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ¬C.gates[↑i].args.length ≤ C.gates[↑i].args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_of_lookup`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_of_lookup : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ) (i : Fin C.gates.length)
  (r j : ℕ) (p : Fin C.gates[↑i].args.length),
  r < (rows i).length →
    (rows i).Nodup →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u)[j]? =
          some (i, r, ↑p) →
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows perm u i
            ((perm i) ((rows i).getD r fun x => false)) p =
          j
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_padded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex_padded : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u q : ℕ) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool) (p : Fin C.gates[↑i].args.length),
  C.gates[↑i].args.Nodup →
    (∀ (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
      C.gates[↑i].args[↑p] = u →
        a p = true →
          ∀
            (hslot :
              TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows perm u i a p < q + 1),
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.padded q
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows perm u)
                ⟨TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows perm u i a p,
                  hslot⟩ =
              some (i, TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.rowIndex C rows perm i a, ↑p)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.direct_sampler`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.direct_sampler : ∀ {L : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool) (E₂ : List Bool → List Bool) (n q : ℕ)
  (offset len : Fin (q + 1) → ℕ) (m : (i : Fin (q + 1)) → Fin (len i) → Bool) (k : Fin n → Bool)
  (r : Fin (q + 1) → Fin n → Bool) (j : Fin (q + 1)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
      (Turing.pairEncode (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q offset len m (k, r))
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord ↑j)) =
    TCSlib.Cryptography.SecureComputation.sliceEnc G n (offset j) k (r j) (List.ofFn (m j))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerCipher_length`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerCipher_length : ∀
  {G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool} {E₁ : List Bool → List Bool},
  (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
    ∀ (n : ℕ) (k o r : Fin n → Bool),
      (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r)).length = 4 * n + 2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerCipher_length._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerCipher_length._proof_1_2 : ∀
  {E₁ : List Bool → List Bool} (n : ℕ) (k o r : Fin n → Bool), ¬2 * n + 2 + (n + n) = 4 * n + 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerCipher_length._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerCipher_length._simp_1_1 : ∀ (n : ℕ),
  (n ≤ n) = True
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerMessage`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerMessage : (List Bool → List Bool) →
  (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → Fin (4 * n + 2) → Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerMessage_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerMessage_eq : ∀
  (E₁ : List Bool → List Bool) (n : ℕ) (k o r : Fin n → Bool) (t : Fin (4 * n + 2)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerMessage E₁ n k o r t =
    (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r)).getD (↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerMessage_ofFn`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerMessage_ofFn : ∀
  {G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool} {E₁ : List Bool → List Bool},
  (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
    ∀ (n : ℕ) (k o r : Fin n → Bool),
      List.ofFn (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.innerMessage E₁ n k o r) =
        TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.inner_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.inner_row : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      ∀ (n : ℕ) (k outer o r₁ r₂ : Fin n → Bool),
        TCSlib.Cryptography.SecureComputation.spEncStr E₂ (List.ofFn outer)
            (TCSlib.Cryptography.SecureComputation.sliceEnc G n 0 k r₂ (List.ofFn o)) (List.ofFn r₁) =
          (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc [outer, k] o (r₁, r₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.only_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.only_row : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      ∀ (n : ℕ) (k o r r₂ : Fin n → Bool),
        TCSlib.Cryptography.SecureComputation.sliceEnc G n 0 k r (List.ofFn o) =
          (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc [k] o (r, r₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.outer_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.outer_row : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
      ∀ (n : ℕ) (k inner o r₁ r₂ : Fin n → Bool),
        TCSlib.Cryptography.SecureComputation.sliceEnc G n (n + n) k r₁
            (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn inner) (List.ofFn o) (List.ofFn r₂)) =
          (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc [k, inner] o (r₁, r₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.slice_shapes_fit`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.slice_shapes_fit : ∀ (n : ℕ),
  0 + n + n ≤ n + n + (n + (4 * n + 2)) ∧ n + n + n + (4 * n + 2) ≤ n + n + (n + (4 * n + 2))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.slice_shapes_fit._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.slice_shapes_fit._proof_1_1 : ∀ (n : ℕ),
  ¬(0 + n + n ≤ n + n + (n + (4 * n + 2)) ∧ n + n + n + (4 * n + 2) ≤ n + n + (n + (4 * n + 2))) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.wrapped_sampler`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.wrapped_sampler : ∀ {L : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool) (E₂ : List Bool → List Bool) (n q : ℕ)
  (offset len : Fin (q + 1) → ℕ) (m : (i : Fin (q + 1)) → Fin (len i) → Bool) (k : Fin n → Bool)
  (r : Fin (q + 1) → Fin n → Bool) (j : Fin (q + 1)) (outer nonce : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
      (Turing.pairEncode (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q offset len m (k, r))
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord (↑j) outer nonce)) =
    TCSlib.Cryptography.SecureComputation.spEncStr E₂ outer
      (TCSlib.Cryptography.SecureComputation.sliceEnc G n (offset j) k (r j) (List.ofFn (m j))) nonce
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.zero_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices.zero_row : ∀ (E₁ E₂ : List Bool → List Bool)
  (n : ℕ) (o r₁ r₂ : Fin n → Bool),
  (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc [] o (r₁, r₂) = List.ofFn o
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.advice_next`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.advice_next : ∀ {m n : ℕ}
  (E₁ E₂ : List Bool → List Bool) (C : BoolCircuit.DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (v : ℕ → Bool),
  C.IsFaninTwo →
    (∀ (i : Fin C.gates.length),
        TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
          v (m + ↑i)) →
      ∀ (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length),
        C.gates[↑i₀].args[↑p] = ↑u →
          ∀ (inA outLen : ℕ) (output : Fin outLen → ℕ) (privateInput aliceOutput : List Bool),
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice C rows s u E₁ E₂
                (fun i a =>
                  TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i)
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + ↑p) i a))
                (Complexity.pairSndD
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message
                    (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C s inA outLen output v
                    (2 * ↑i₀ + ↑p)))
                privateInput aliceOutput =
              TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice C rows s u E₁ E₂
                (fun i a =>
                  TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i)
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + ↑p + 1) i
                      a))
                (Complexity.pairSndD
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message
                    (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C s inA outLen output v
                    (2 * ↑i₀ + ↑p + 1)))
                privateInput aliceOutput
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.advice_next._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.advice_next._proof_1_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (u : Fin C.size) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.plaintext_ne`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.plaintext_ne : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool) (i₀ : Fin C.gates.length),
  ∀ u ∈ C.gates[↑i₀].args,
    ∀ phase ≤ 2,
      ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
        (m + ↑i, TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + phase) i a) ≠
          (u, true)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.plaintext_ne._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.plaintext_ne._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.plaintext_ne._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.plaintext_ne._proof_1_1 : ∀ phase ≤ 2,
  ¬(phase = 0 ∨ phase = 1 ∨ phase = 2) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.plaintext_ne._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.plaintext_ne._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (phase : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
        ∀ {m n : ℕ} (C : BoolCircuit.DAGCircuit m)
          (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
          (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
          (u : Fin C.size) (q : ℕ) (v : ℕ → Bool),
          C.IsFaninTwo →
            (∀ (i : Fin C.gates.length),
                TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
                  v (m + ↑i)) →
              ∀ (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length),
                C.gates[↑i₀].args[↑p] = ↑u →
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2
                          ↑u).length ≤
                      q + 1 →
                    (∀ (i : Fin C.gates.length), rows i = Finset.univ.toList) →
                      ∀ (inA inB outLen : ℕ) (output : Fin outLen → ℕ),
                        (∀ (j : Fin outLen), ∀ g ∈ C.gates, output j ∉ g.args) →
                          ∀ (N bobInput aliceOutput : List Bool) (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool)
                            (side : Bool),
                            have before := 2 * ↑i₀ + ↑p;
                            have stage := before + side.toNat;
                            have plain := fun i a =>
                              TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i)
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v stage i
                                  a);
                            have beta :=
                              TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice C rows s u E₁ E₂
                                (fun i a =>
                                  TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i)
                                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v
                                      before i a))
                                (Complexity.pairSndD
                                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message
                                    (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C s inA outLen output
                                    v before))
                                (Turing.pairEncode bobInput
                                  (List.ofFn
                                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers C s
                                      inA inB)))
                                aliceOutput;
                            TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild E₂
                                (Turing.pairEncode N
                                  (Turing.pairEncode
                                    (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q
                                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C
                                        rows s u q)
                                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C
                                        rows s u q)
                                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage C
                                        rows s u q E₁ plain)
                                      (k, rs))
                                    beta)) =
                              TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                                (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k
                                  rs)
                                inA inB outLen output v N bobInput [] aliceOutput stage
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_1 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (_x_4 : ∀ (i : Fin C.gates.length), ↑i < C.gates.length)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (i₀ : Fin C.gates.length) (_x_2 : ↑i₀ < C.gates.length) (p : Fin C.gates[↑i₀].args.length),
  ¬C.gates.length ≤ C.gates.length → ∀ (_x_1 : ↑i₀ < C.gates.length), ↑p < C.gates[↑i₀].args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_1_1 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length),
  C.gates[↑i₀].args.length ≤ 2 → ↑p < C.gates[↑i₀].args.length → ¬↑p ≤ 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_1_2 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length), ↑p ≤ 1 → ¬↑p ≤ 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_1_3 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length), ↑p ≤ 1 → ¬↑p + 1 ≤ 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.reconstruct._proof_2 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (v : ℕ → Bool),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    (∀ (i : Fin C.gates.length),
        TCSlib.Cryptography.SecureComputation.gateOut C.gates[i]
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues C v i) =
          v (m + ↑i)) →
      ∀ (i₀ : Fin C.gates.length),
        C.gates[↑i₀].args.Nodup →
          ∀ (p : Fin C.gates[↑i₀].args.length) (u : ℕ),
            C.gates[↑i₀].args[↑p] = u →
              ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.selectedPosition C.gates[↑i] a u =
                    none →
                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + ↑p) i a =
                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v (2 * ↑i₀ + ↑p + 1) i a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i₀ : Fin C.gates.length), ¬C.gates[↑i₀].args.length ≤ C.gates[↑i₀].args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_1_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length) (u : ℕ),
  C.gates[↑i₀].args.length ≤ 2 → ↑p < C.gates[↑i₀].args.length → ¬↑p ≤ 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_1_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length) (u : ℕ),
  ↑p ≤ 1 → ¬↑p = 0 → ¬↑p = 1 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_1_3 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length) (u : ℕ),
  ¬2 * ↑i₀ + 1 + 1 = 2 * ↑i₀ + 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep.unselected_eq._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i₀ : Fin C.gates.length) (p : Fin C.gates[↑i₀].args.length) (u : ℕ),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice : (ℕ → Type) →
  {inputs : ℕ → ℕ} → ((n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) → Complexity.PolyExpr → ℕ → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice_eq : ∀ (I : ℕ → Type)
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr) (n : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n =
    (Option (I n × TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n)) ×
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection : {m : ℕ} →
  BoolCircuit.DAGCircuit m → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection C =
    ((i : Fin C.gates.length) × Fin C.gates[↑i].args.length)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape : Complexity.PolyExpr → ℕ → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape_eq : ∀ (S : Complexity.PolyExpr)
  (n : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n =
    (Fin (10 * S.eval n * n + 2 * S.eval n) → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice : {I : ℕ → Type} →
  {inputs : ℕ → ℕ} →
    (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) →
      (S : Complexity.PolyExpr) →
        Complexity.PolyExpr →
          Complexity.PolyExpr →
            (O : Complexity.PolyExpr) →
              ((n : ℕ) →
                  List Bool →
                    TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool)
                      ((Fin n → Bool) × (Fin n → Bool))) →
                ((n : ℕ) → I n → ℕ → Bool) →
                  ((n : ℕ) → Fin (O.eval n) → ℕ) →
                    ((n : ℕ) → I n → List Bool) →
                      ((n : ℕ) → I n → List Bool) →
                        (List Bool → List Bool) →
                          (List Bool → List Bool) →
                            (n : ℕ) →
                              TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n →
                                List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice_budget`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice_budget : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S A B O : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (output : (n : ℕ) → Fin (O.eval n) → ℕ) (bobWord aliceWord : (n : ℕ) → I n → List Bool)
  (E₁ E₂ : List Bool → List Bool) (R : Complexity.PolyExpr),
  (∀ (n : ℕ), (C n).size ≤ S.eval n) →
    (∀ (n : ℕ), (C n).IsFaninTwo) →
      (∀ (n : ℕ) (z : I n), (bobWord n z).length ≤ B.eval n) →
        (∀ (n : ℕ) (z : I n), (aliceWord n z).length ≤ R.eval n) →
          ∀ (n : ℕ) (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n),
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice C S A B O seed v output
                  bobWord aliceWord E₁ E₂ n a).length ≤
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.sampleBudget S A B O R).eval n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice_none`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice_none : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S A B O : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (output : (n : ℕ) → Fin (O.eval n) → ℕ) (bobWord aliceWord : (n : ℕ) → I n → List Bool)
  (E₁ E₂ : List Bool → List Bool) (n : ℕ)
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice C S A B O seed v output bobWord
      aliceWord E₁ E₂ n (none, t) =
    []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice_some`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice_some : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S A B O : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (output : (n : ℕ) → Fin (O.eval n) → ℕ) (bobWord aliceWord : (n : ℕ) → I n → List Bool)
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (z : I n)
  (b : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n))
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice C S A B O seed v output bobWord
      aliceWord E₁ E₂ n (some (z, b), t) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice (C n)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b) E₁ E₂
      (fun i a =>
        TCSlib.Cryptography.SecureComputation.keyAt (C n) (seed n (List.ofFn t)) (inputs n + ↑i)
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit (C n) (v n z) (2 * ↑b.fst + ↑b.snd)
            i a))
      (Complexity.pairSndD
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message
          (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn t)) (A.eval n)
          (O.eval n) (output n) (v n z) (2 * ↑b.fst + ↑b.snd)))
      (Turing.pairEncode (bobWord n z)
        (List.ofFn
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers (C n) (seed n (List.ofFn t))
            (A.eval n) (B.eval n))))
      (aliceWord n z)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.capacity`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.capacity : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : Complexity.PolyExpr) (n : ℕ)
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ),
  C.size ≤ S.eval n →
    C.IsFaninTwo →
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows C) perm u).length ≤
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n + 1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.capacity._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.capacity._proof_1_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : Complexity.PolyExpr) (n : ℕ)
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ),
  m + C.gates.length ≤ S.eval n → ¬C.gates.length ≤ S.eval n → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.capacity._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.capacity._proof_1_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : Complexity.PolyExpr) (n : ℕ)
  (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)) (u : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows C) perm u).length ≤
      4 * C.gates.length →
    C.gates.length ≤ S.eval n →
      ¬(TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows C) perm u).length ≤
            4 * S.eval n + 1 →
        False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.fits`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.fits : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (L : Complexity.PolyExpr),
  (∀ (n : ℕ), 7 * n + 2 ≤ L.eval n) →
    ∀ (n : ℕ) (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n)
      (j : Fin ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n + 1)),
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset C S seed n a j + n +
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len C S seed n a j ≤
        L.eval n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.fits._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.fits._proof_1_1 : ∀
  (L : Complexity.PolyExpr) (n : ℕ), 7 * n + 2 ≤ L.eval n → ¬0 + n + 0 ≤ L.eval n → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.fits._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.fits._proof_1_2 : ∀ {inputs : ℕ → ℕ}
  (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (L : Complexity.PolyExpr) (n : ℕ)
  (j : Fin ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n + 1))
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n)
  (b : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset (C n)
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b)
            ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n) j +
          n +
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength (C n)
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b)
          ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n) j ≤
      n + n + (n + (4 * n + 2)) →
    7 * n + 2 ≤ L.eval n →
      ¬TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset (C n)
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n))
                  (seed n (List.ofFn t))
                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b)
                  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n) j +
                n +
              TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength (C n)
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n))
                (seed n (List.ofFn t))
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b)
                ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n) j ≤
            L.eval n →
        False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len : {I : ℕ → Type} →
  {inputs : ℕ → ℕ} →
    (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) →
      (S : Complexity.PolyExpr) →
        ((n : ℕ) →
            List Bool →
              TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))) →
          (n : ℕ) →
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n →
              Fin
                  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n +
                    1) →
                ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len_none`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len_none : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (n : ℕ) (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len C S seed n (none, t) = fun x => 0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len_some`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len_some : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (n : ℕ) (z : I n) (b : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n))
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len C S seed n (some (z, b), t) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength (C n)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b)
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message : {I : ℕ → Type} →
  {inputs : ℕ → ℕ} →
    (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) →
      (S : Complexity.PolyExpr) →
        (seed :
            (n : ℕ) →
              List Bool →
                TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool)
                  ((Fin n → Bool) × (Fin n → Bool))) →
          ((n : ℕ) → I n → ℕ → Bool) →
            (List Bool → List Bool) →
              Bool →
                (n : ℕ) →
                  (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n) →
                    (j :
                        Fin
                          ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval
                              n +
                            1)) →
                      Fin
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len C S seed n a
                            j) →
                        Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message._proof_1 : ∀ {inputs : ℕ → ℕ}
  (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (n : ℕ) (i : Fin (C n).gates.length), ↑i < (C n).gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message._proof_2 : ∀ {inputs : ℕ → ℕ}
  (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (n : ℕ)
  (b : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n)),
  ↑b.fst < (C n).gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message_none`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message_none : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (E₁ : List Bool → List Bool) (side : Bool) (n : ℕ)
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message C S seed v E₁ side n (none, t) =
    fun x x_1 => false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message_some`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message_some : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (E₁ : List Bool → List Bool) (side : Bool) (n : ℕ) (z : I n)
  (b : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n))
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message C S seed v E₁ side n
      (some (z, b), t) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage (C n)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b)
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n) E₁ fun i a =>
      TCSlib.Cryptography.SecureComputation.keyAt (C n) (seed n (List.ofFn t)) (inputs n + ↑i)
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit (C n) (v n z)
          (2 * ↑b.fst + ↑b.snd + side.toNat) i a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset : {I : ℕ → Type} →
  {inputs : ℕ → ℕ} →
    (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) →
      (S : Complexity.PolyExpr) →
        ((n : ℕ) →
            List Bool →
              TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))) →
          (n : ℕ) →
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n →
              Fin
                  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n +
                    1) →
                ℕ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset.match_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset.match_1 : {I : ℕ → Type} →
  {inputs : ℕ → ℕ} →
    (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) →
      (S : Complexity.PolyExpr) →
        (n : ℕ) →
          (motive :
              TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n → Sort u_1) →
            (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Choice I C S n) →
              ((snd : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n) →
                  motive (none, snd)) →
                ((fst : I n) →
                    (b : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n)) →
                      (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n) →
                        motive (some (fst, b), t)) →
                  motive a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset_none`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset_none : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (n : ℕ) (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset C S seed n (none, t) = fun x => 0
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset_some`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset_some : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (n : ℕ) (z : I n) (b : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n))
  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset C S seed n (some (z, b), t) =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset (C n)
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b)
      ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval n)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rebuild_some`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rebuild_some : ∀ {I : ℕ → Type}
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (S A B O : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (output : (n : ℕ) → Fin (O.eval n) → ℕ) (bobWord aliceWord : (n : ℕ) → I n → List Bool)
  (E₁ E₂ : List Bool → List Bool) {L : Complexity.PolyExpr} {L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L.eval n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
        (∀ (n : ℕ), (C n).size ≤ S.eval n) →
          (∀ (n : ℕ), (C n).IsFaninTwo) →
            (∀ (n : ℕ) (z : I n) (i : Fin (C n).gates.length),
                TCSlib.Cryptography.SecureComputation.gateOut (C n).gates[i]
                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues (C n) (v n z) i) =
                  v n z (inputs n + ↑i)) →
              (∀ (n : ℕ) (j : Fin (O.eval n)), ∀ g ∈ (C n).gates, output n j ∉ g.args) →
                ∀ (n : ℕ) (z : I n)
                  (b : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection (C n))
                  (t : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S n)
                  (k : Fin n → Bool)
                  (rs :
                    Fin
                        ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval
                            n +
                          1) →
                      Fin n → Bool)
                  (side : Bool),
                  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild E₂
                      (Turing.pairEncode (List.replicate n true)
                        (Turing.pairEncode
                          (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n
                            ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget
                                  S).eval
                              n)
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.offset C S seed n
                              (some (z, b), t))
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.len C S seed n
                              (some (z, b), t))
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.message C S seed v
                              E₁ side n (some (z, b), t))
                            (k, rs))
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.advice C S A B O
                            seed v output bobWord aliceWord E₁ E₂ n (some (z, b), t)))) =
                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (C n)
                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill (C n)
                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows (C n))
                        (seed n (List.ofFn t))
                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire (C n) b)
                        ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget S).eval
                          n)
                        k rs)
                      (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true) (bobWord n z) []
                      (aliceWord n z) (2 * ↑b.fst + ↑b.snd + side.toNat)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rebuild_some._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rebuild_some._proof_1 : ∀
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (n : ℕ),
  ¬(C n).gates.length ≤ (C n).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) → (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows_complete`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows_complete : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
  a ∈ TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows C i
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows C i = Finset.univ.toList
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows_nodup`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows_nodup : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows C i).Nodup
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection C → Fin C.size
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m)
  (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection C),
  ¬C.gates[↑a.fst].args.length ≤ C.gates[↑a.fst].args.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m)
  (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection C),
  C.gates[↑a.fst].args[↑a.snd] < m + ↑a.fst → ¬C.gates[↑a.fst].args[↑a.snd] < m + C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_3 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m)
  (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection C), ↑a.fst < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_4 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m)
  (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection C),
  ↑a.snd < C.gates[↑a.fst].args.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_5`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire._proof_5 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m)
  (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection C),
  C.gates[↑a.fst].args[↑a.snd] < C.size
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire_val`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire_val : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m)
  (a : TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection C),
  ↑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire C a) = C.gates[↑a.fst].args[↑a.snd]
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepSecurity.filled_negligible`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepSecurity.filled_negligible : ∀ {I : ℕ → Type}
  [(n : ℕ) → Fintype (I n)] {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n))
  (S A B O R : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (output : (n : ℕ) → Fin (O.eval n) → ℕ)
  (bobWord aliceWord : (n : ℕ) → I n → List Bool),
  (∀ (n : ℕ), (C n).size ≤ S.eval n) →
    (∀ (n : ℕ), (C n).IsFaninTwo) →
      (∀ (n : ℕ) (z : I n) (i : Fin (C n).gates.length),
          TCSlib.Cryptography.SecureComputation.gateOut (C n).gates[i]
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues (C n) (v n z) i) =
            v n z (inputs n + ↑i)) →
        (∀ (n : ℕ) (j : Fin (O.eval n)), ∀ g ∈ (C n).gates, output n j ∉ g.args) →
          (∀ (n : ℕ) (z : I n), (bobWord n z).length ≤ B.eval n) →
            (∀ (n : ℕ) (z : I n), (aliceWord n z).length ≤ R.eval n) →
              ∀ {L : Complexity.PolyExpr} {L₂ : ℕ → ℕ}
                (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L.eval n) → Bool)
                (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
                (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
                Complexity.PolyTimeComputable E₂ →
                  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
                    (∀ (n : ℕ) (s x : Fin n → Bool),
                        E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
                      (∀ (n : ℕ) (s x : Fin n → Bool),
                          E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
                        (∀ (n : ℕ), 7 * n + 2 ≤ L.eval n) →
                          TCSlib.Cryptography.SecureComputation.SliceMultiMessageSecure G →
                            ∀ (D : Complexity.NUPPT),
                              ∃ μ,
                                TCSlib.Cryptography.Negligible μ ∧
                                  (∀ (n : ℕ), 0 ≤ μ n) ∧
                                    ∀ (n : ℕ) (z : I n)
                                      (b :
                                        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Selection
                                          (C n))
                                      (t :
                                        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.Tape S
                                          n),
                                      TCSlib.Cryptography.distAdv
                                          (fun r =>
                                            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                                              (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (C n)
                                              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill
                                                (C n)
                                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows
                                                  (C n))
                                                (seed n (List.ofFn t))
                                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire
                                                  (C n) b)
                                                ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget
                                                      S).eval
                                                  n)
                                                r.1 r.2)
                                              (A.eval n) (B.eval n) (O.eval n) (output n) (v n z)
                                              (List.replicate n true) (bobWord n z) [] (aliceWord n z)
                                              (2 * ↑b.fst + ↑b.snd))
                                          (fun r =>
                                            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                                              (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (C n)
                                              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill
                                                (C n)
                                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.rows
                                                  (C n))
                                                (seed n (List.ofFn t))
                                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices.wire
                                                  (C n) b)
                                                ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds.slotBudget
                                                      S).eval
                                                  n)
                                                r.1 r.2)
                                              (A.eval n) (B.eval n) (O.eval n) (output n) (v n z)
                                              (List.replicate n true) (bobWord n z) [] (aliceWord n z)
                                              (2 * ↑b.fst + ↑b.snd + 1))
                                          (D.distinguisherL n) ≤
                                        μ n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepSecurity.selected_negligible`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepSecurity.selected_negligible : ∀ {I : ℕ → Type}
  [(n : ℕ) → Fintype (I n)] {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n))
  (S A B O R : Complexity.PolyExpr)
  (seed :
    (n : ℕ) →
      List Bool →
        TCSlib.Cryptography.SecureComputation.GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : (n : ℕ) → I n → ℕ → Bool) (output : (n : ℕ) → Fin (O.eval n) → ℕ)
  (bobWord aliceWord : (n : ℕ) → I n → List Bool),
  (∀ (n : ℕ), (C n).size ≤ S.eval n) →
    (∀ (n : ℕ), (C n).IsFaninTwo) →
      (∀ (n : ℕ) (z : I n) (i : Fin (C n).gates.length),
          TCSlib.Cryptography.SecureComputation.gateOut (C n).gates[i]
              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues (C n) (v n z) i) =
            v n z (inputs n + ↑i)) →
        (∀ (n : ℕ) (j : Fin (O.eval n)), ∀ g ∈ (C n).gates, output n j ∉ g.args) →
          (∀ (n : ℕ) (z : I n), (bobWord n z).length ≤ B.eval n) →
            (∀ (n : ℕ) (z : I n), (aliceWord n z).length ≤ R.eval n) →
              ∀ {L : Complexity.PolyExpr} {L₂ : ℕ → ℕ}
                (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L.eval n) → Bool)
                (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
                (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
                Complexity.PolyTimeComputable E₂ →
                  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
                    (∀ (n : ℕ) (s x : Fin n → Bool),
                        E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
                      (∀ (n : ℕ) (s x : Fin n → Bool),
                          E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
                        (∀ (n : ℕ), 7 * n + 2 ≤ L.eval n) →
                          TCSlib.Cryptography.SecureComputation.SliceMultiMessageSecure G →
                            (∀ (n : ℕ) (q : List Bool) (w : Fin (C n).size) (b : Bool) (t : Fin n),
                                (seed n q).1 w b t = q.getD ((b.toNat * S.eval n + ↑w) * n + ↑t) false) →
                              (∀ (n : ℕ) (q : List Bool) (i : Fin (C n).gates.length)
                                  (a : Fin (C n).gates[↑i].args.length → Bool) (t : Fin n),
                                  ((seed n q).2.1 i a).1 t =
                                    q.getD
                                      (2 * S.eval n * n +
                                          (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) +
                                        ↑t)
                                      false) →
                                (∀ (n : ℕ) (q : List Bool) (i : Fin (C n).gates.length)
                                    (a : Fin (C n).gates[↑i].args.length → Bool) (t : Fin n),
                                    ((seed n q).2.1 i a).2 t =
                                      q.getD
                                        (2 * S.eval n * n +
                                              (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) *
                                                (2 * n) +
                                            n +
                                          ↑t)
                                        false) →
                                  (∀ (n : ℕ) (q : List Bool) (i : Fin (C n).gates.length)
                                      (a : Fin (C n).gates[↑i].args.length → Bool)
                                      (t : Fin (C n).gates[↑i].args.length),
                                      ((seed n q).2.2 i) a t =
                                        (a t ^^ q.getD (10 * S.eval n * n + 2 * ↑i + ↑t) false)) →
                                    ∀ (D : Complexity.NUPPT),
                                      ∃ μ,
                                        TCSlib.Cryptography.Negligible μ ∧
                                          (∀ (n : ℕ), 0 ≤ μ n) ∧
                                            ∀ (n : ℕ) (z : I n) (i : Fin (C n).gates.length)
                                              (p : Fin (C n).gates[↑i].args.length),
                                              TCSlib.Cryptography.distAdv
                                                  (fun t =>
                                                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                                                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n)
                                                      (C n) (seed n (List.ofFn t)) (A.eval n) (B.eval n) (O.eval n)
                                                      (output n) (v n z) (List.replicate n true) (bobWord n z) []
                                                      (aliceWord n z) (2 * ↑i + ↑p))
                                                  (fun t =>
                                                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                                                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n)
                                                      (C n) (seed n (List.ofFn t)) (A.eval n) (B.eval n) (O.eval n)
                                                      (output n) (v n z) (List.replicate n true) (bobWord n z) []
                                                      (aliceWord n z) (2 * ↑i + ↑p + 1))
                                                  (D.distinguisherL n) ≤
                                                μ n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepSecurity.selected_negligible._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepSecurity.selected_negligible._proof_1_1 : ∀
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (n : ℕ) (j : Fin (C n).gates.length),
  ¬↑j < (C n).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.record_reconstruct`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.record_reconstruct : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
        ∀ {m n : ℕ} (C : BoolCircuit.DAGCircuit m)
          (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
          (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
          (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
          (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
            (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
              (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2
                        ↑u).length ≤
                    q + 1 →
                  ∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (k : Fin n → Bool)
                    (rs : Fin (q + 1) → Fin n → Bool),
                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
                        (Turing.pairEncode
                          (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C rows s u q)
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u q)
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage C rows s u q
                              E₁ o)
                            (k, rs))
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.record C rows s u E₁ E₂ o i
                            a)) =
                      (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc
                        (TCSlib.Cryptography.SecureComputation.argKeys C
                          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs) i
                          a)
                        (o i a)
                        ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs).2.1
                          i a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.record_reconstruct._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.record_reconstruct._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.record_reconstruct._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.record_reconstruct._proof_1_1 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool)
  (p : Fin C.gates[↑i].args.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.slotIndex C rows s.2.2 (↑u) i a p < q + 1 →
    ¬↑i < C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.record_reconstruct._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.record_reconstruct._proof_2 : ∀ {m n : ℕ}
  (C : BoolCircuit.DAGCircuit m) (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.sample_reconstruct`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.sample_reconstruct : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
        ∀ {m n : ℕ} (C : BoolCircuit.DAGCircuit m)
          (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
          (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
          (u : Fin C.size) (q inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ)
          (N bobInput aliceOutput : List Bool),
          (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
            (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
              (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2
                        ↑u).length ≤
                    q + 1 →
                  (∀ (i : Fin C.gates.length), rows i = Finset.univ.toList) →
                    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
                        (m + ↑i,
                            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v stage i a) ≠
                          (↑u, true)) →
                      (∀ (j : Fin outLen), output j ≠ ↑u) →
                        ∀ (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool),
                          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild E₂
                              (Turing.pairEncode N
                                (Turing.pairEncode
                                  (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q
                                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C rows
                                      s u q)
                                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows
                                      s u q)
                                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage C
                                      rows s u q E₁ fun i a =>
                                      TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i)
                                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v
                                          stage i a))
                                    (k, rs))
                                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.advice C rows s u
                                    E₁ E₂
                                    (fun i a =>
                                      TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i)
                                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit C v
                                          stage i a))
                                    (Complexity.pairSndD
                                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message
                                        (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C s inA outLen
                                        output v stage))
                                    (Turing.pairEncode bobInput
                                      (List.ofFn
                                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects.activeAnswers
                                          C s inA inB)))
                                    aliceOutput))) =
                            TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
                              (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C
                              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k rs)
                              inA inB outLen output v N bobInput [] aliceOutput stage
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.tablesWith_reconstruct`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.tablesWith_reconstruct : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
        ∀ {m n : ℕ} (C : BoolCircuit.DAGCircuit m)
          (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
          (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
          (u : Fin C.size) (q : ℕ) (bit : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Bool),
          (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
            (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
              (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2
                        ↑u).length ≤
                    q + 1 →
                  (∀ (i : Fin C.gates.length), rows i = Finset.univ.toList) →
                    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
                        (m + ↑i, bit i a) ≠ (↑u, true)) →
                      ∀ (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool),
                        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂
                            (Turing.pairEncode
                              (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C rows s u
                                  q)
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u
                                  q)
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage C rows s
                                  u q E₁ fun i a => TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i) (bit i a))
                                (k, rs))
                              (Complexity.BinArith.encWords
                                (List.map Complexity.BinArith.encWords
                                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u
                                    E₁ E₂ fun i a =>
                                    TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i) (bit i a))))) =
                          Complexity.BinArith.encWords
                            (List.ofFn fun i =>
                              Complexity.BinArith.encWords
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith
                                  (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C
                                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q k
                                    rs)
                                  bit i))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.tables_reconstruct`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.tables_reconstruct : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
        ∀ {m n : ℕ} (C : BoolCircuit.DAGCircuit m)
          (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
          (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
          (u : Fin C.size) (q : ℕ) (o : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Fin n → Bool),
          (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
            (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
              (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2
                        ↑u).length ≤
                    q + 1 →
                  ∀ (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool),
                    TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂
                        (Turing.pairEncode
                          (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C rows s u q)
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s u q)
                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage C rows s u q
                              E₁ o)
                            (k, rs))
                          (Complexity.BinArith.encWords
                            (List.map Complexity.BinArith.encWords
                              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s u E₁ E₂
                                o)))) =
                      Complexity.BinArith.encWords
                        (List.ofFn fun i =>
                          Complexity.BinArith.encWords
                            (List.map
                              (fun a =>
                                (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc
                                  (TCSlib.Cryptography.SecureComputation.argKeys C
                                    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q
                                      k rs)
                                    i ((s.2.2 i) a))
                                  (o i ((s.2.2 i) a))
                                  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C rows s u q
                                          k rs).2.1
                                    i ((s.2.2 i) a)))
                              (rows i)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.view_reconstruct`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables.view_reconstruct : ∀ {L L₂ : ℕ → ℕ}
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L n) → Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L₂ n) → Bool) (E₁ E₂ : List Bool → List Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
      (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
        ∀ {m n : ℕ} (C : BoolCircuit.DAGCircuit m)
          (rows : (i : Fin C.gates.length) → List (Fin C.gates[↑i].args.length → Bool))
          (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
          (u : Fin C.size) (q : ℕ) (bit : (i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → Bool),
          (∀ (i : Fin C.gates.length), C.gates[↑i].args.Nodup) →
            (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
              (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool), a ∈ rows i) →
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences.occurrences C rows s.2.2
                        ↑u).length ≤
                    q + 1 →
                  (∀ (i : Fin C.gates.length), rows i = Finset.univ.toList) →
                    (∀ (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
                        (m + ↑i, bit i a) ≠ (↑u, true)) →
                      ∀ (N tail privateInput aliceOutput : List Bool) (k : Fin n → Bool)
                        (rs : Fin (q + 1) → Fin n → Bool),
                        TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild E₂
                            (Turing.pairEncode N
                              (Turing.pairEncode
                                (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n q
                                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotOffset C rows s
                                    u q)
                                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotLength C rows s
                                    u q)
                                  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.slotMessage C rows
                                    s u q E₁ fun i a =>
                                    TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i) (bit i a))
                                  (k, rs))
                                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice
                                  (Complexity.BinArith.encWords
                                    (List.map Complexity.BinArith.encWords
                                      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan.tables C rows s
                                        u E₁ E₂ fun i a =>
                                        TCSlib.Cryptography.SecureComputation.keyAt C s (m + ↑i) (bit i a))))
                                  tail privateInput aliceOutput))) =
                          Turing.pairEncode
                            { x := N, z := privateInput, r := [],
                                received :=
                                  [Turing.pairEncode
                                      (Complexity.BinArith.encWords
                                        (List.ofFn fun i =>
                                          Complexity.BinArith.encWords
                                            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith
                                              (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C
                                              (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed.fill C
                                                rows s u q k rs)
                                              bit i)))
                                      tail] }.encode
                            aliceOutput
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice : List Bool →
  List Bool → List Bool → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice_eq : ∀ (d t x a : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice d t x a =
    Turing.pairEncode d (Turing.pairEncode t (Turing.pairEncode x a))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice_length`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice_length : ∀
  (d t x a : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice d t x a).length =
    2 * d.length + 2 * t.length + 2 * x.length + a.length + 6
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice_length._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice_length._proof_1_1 : ∀
  (d t x a : List Bool),
  ¬2 * d.length + 2 + (2 * t.length + 2 + (2 * x.length + 2 + a.length)) =
        2 * d.length + 2 * t.length + 2 * x.length + a.length + 6 →
    False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord : ℕ → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord_eq : ∀ (j : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord j =
    Turing.pairEncode [true] (Turing.pairEncode (List.replicate j true) [])
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.encodeList_eq_encWords`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.encodeList_eq_encWords : ∀
  (cs : List (List Bool)), TCSlib.Cryptography.PrivateKeyScheme.encodeList cs = Complexity.BinArith.encWords cs
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.fixedRecord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.fixedRecord : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.fixedRecord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.fixedRecord_eq : ∀ (c : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.fixedRecord c = Turing.pairEncode [] c
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild_eq : ∀
  (E₂ : List Bool → List Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild E₂ z =
    have data := Complexity.pairSndD (Complexity.pairSndD z);
    have rest := Complexity.pairSndD data;
    have message :=
      Turing.pairEncode
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂
          (Turing.pairEncode (Complexity.pairFstD (Complexity.pairSndD z)) (Complexity.pairFstD data)))
        (Complexity.pairFstD rest);
    Turing.pairEncode
      { x := Complexity.pairFstD z, z := Complexity.pairFstD (Complexity.pairSndD rest), r := [],
          received := [message] }.encode
      (Complexity.pairSndD (Complexity.pairSndD rest))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild_layout`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild_layout : ∀
  (E₂ : List Bool → List Bool) (N challenge d t x a : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild E₂
      (Turing.pairEncode N
        (Turing.pairEncode challenge
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.advice d t x a))) =
    Turing.pairEncode
      { x := N, z := x, r := [],
          received :=
            [Turing.pairEncode
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂
                  (Turing.pairEncode challenge d))
                t] }.encode
      a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild_poly : ∀
  {E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₂ →
    Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.rebuild E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.record_lengths`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.record_lengths : ∀ (c : List Bool)
  (j : ℕ) (k r : List Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.fixedRecord c).length = c.length + 2 ∧
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord j).length = 2 * j + 6 ∧
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord j k r).length =
        2 * j + 2 * k.length + r.length + 8
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.record_lengths._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.record_lengths._proof_1_1 : ∀
  (c : List Bool) (j : ℕ) (k r : List Bool),
  ¬(2 * 0 + 2 + c.length = c.length + 2 ∧
        2 * (0 + 1) + 2 + (2 * j + 2 + 0) = 2 * j + 6 ∧
          2 * (0 + 1) + 2 + (2 * j + 2 + (2 * k.length + 2 + r.length)) = 2 * j + 2 * k.length + r.length + 8) →
    False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_directRecord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_directRecord : ∀
  (E₂ : List Bool → List Bool) (challenge : List (List Bool)) (j : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
      (Turing.pairEncode (Complexity.BinArith.encWords challenge)
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.directRecord j)) =
    challenge.getD j []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_directRecord._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_directRecord._simp_1_1 : ∀
  {α : Type u_1} (a : α) (l : List α), (a :: l = []) = False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_eq : ∀ (E₂ : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂ z =
    have descriptor := Complexity.pairSndD z;
    have tag := Complexity.pairFstD descriptor;
    have data := Complexity.pairSndD descriptor;
    have c := (Complexity.BinArith.decWords (Complexity.pairFstD z)).getD (Complexity.pairFstD data).length [];
    if tag = [] then data
    else
      if tag = [true] then c
      else
        TCSlib.Cryptography.SecureComputation.spEncStr E₂ (Complexity.pairFstD (Complexity.pairSndD data)) c
          (Complexity.pairSndD (Complexity.pairSndD data))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_fixedRecord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_fixedRecord : ∀
  (E₂ : List Bool → List Bool) (challenge c : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
      (Turing.pairEncode challenge
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.fixedRecord c)) =
    c
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_poly : ∀
  {E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₂ →
    Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_wrappedRecord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_wrappedRecord : ∀
  (E₂ : List Bool → List Bool) (challenge : List (List Bool)) (j : ℕ) (k r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
      (Turing.pairEncode (Complexity.BinArith.encWords challenge)
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord j k r)) =
    TCSlib.Cryptography.SecureComputation.spEncStr E₂ k (challenge.getD j []) r
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_wrappedRecord._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row_wrappedRecord._simp_1_1 : ∀
  {α : Type u_1} (a : α) (l : List α), (a :: l = []) = False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table_eq : ∀
  (E₂ : List Bool → List Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table E₂ z =
    Complexity.BinArith.mapW (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂) z
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table_pairEncode`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table_pairEncode : ∀
  (E₂ : List Bool → List Bool) (challenge descriptors : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table E₂
      (Turing.pairEncode challenge descriptors) =
    Complexity.BinArith.encWords
      (List.map
        (fun d =>
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
            (Turing.pairEncode challenge d))
        (Complexity.BinArith.decWords descriptors))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table_poly : ∀
  {E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₂ →
    Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_encoded : ∀
  (E₂ : List Bool → List Bool) (challenge : List (List Bool)) (descriptors : List (List (List Bool))),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂
      (Turing.pairEncode (Complexity.BinArith.encWords challenge)
        (Complexity.BinArith.encWords (List.map Complexity.BinArith.encWords descriptors))) =
    Complexity.BinArith.encWords
      (List.map
        (fun ds =>
          Complexity.BinArith.encWords
            (List.map
              (fun d =>
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
                  (Turing.pairEncode (Complexity.BinArith.encWords challenge) d))
              ds))
        descriptors)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_eq : ∀
  (E₂ : List Bool → List Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂ z =
    Complexity.BinArith.mapW (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table E₂) z
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_pairEncode`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_pairEncode : ∀
  (E₂ : List Bool → List Bool) (challenge descriptors : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂
      (Turing.pairEncode challenge descriptors) =
    Complexity.BinArith.encWords
      (List.map
        (fun d =>
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.table E₂
            (Turing.pairEncode challenge d))
        (Complexity.BinArith.decWords descriptors))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_poly : ∀
  {E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₂ →
    Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_records`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables_records : ∀
  (E₂ : List Bool → List Bool) (challenge : List Bool) (descriptors : List (List (List Bool))),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.tables E₂
      (Turing.pairEncode challenge (Complexity.BinArith.encWords (List.map Complexity.BinArith.encWords descriptors))) =
    Complexity.BinArith.encWords
      (List.map
        (fun ds =>
          Complexity.BinArith.encWords
            (List.map
              (fun d =>
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.row E₂
                  (Turing.pairEncode challenge d))
              ds))
        descriptors)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord : ℕ →
  List Bool → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord_eq : ∀ (j : ℕ)
  (k r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction.wrappedRecord j k r =
    Turing.pairEncode [false] (Turing.pairEncode (List.replicate j true) (Turing.pairEncode k r))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.chain_negligible`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.chain_negligible : ∀ {I : ℕ → Type u_1}
  {σ : ℕ → Type u_2} [inst : (n : ℕ) → Fintype (σ n)] (H : (n : ℕ) → I n → ℕ → σ n → List Bool) (D : Complexity.NUPPT)
  (steps : ℕ → ℕ) (p : Complexity.PolyExpr),
  (∀ (n : ℕ), steps n ≤ p.eval n) →
    ∀ {μ : ℕ → ℝ},
      TCSlib.Cryptography.Negligible μ →
        (∀ (n : ℕ) (a : I n),
            ∀ i < steps n, TCSlib.Cryptography.distAdv (H n a i) (H n a (i + 1)) (D.distinguisherL n) ≤ μ n) →
          ∃ ε,
            TCSlib.Cryptography.Negligible ε ∧
              ∀ (n : ℕ) (a : I n), TCSlib.Cryptography.distAdv (H n a 0) (H n a (steps n)) (D.distinguisherL n) ≤ ε n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.distAdv_chain_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.distAdv_chain_le : ∀ {σ : Type u_1}
  {γ : Type u_2} {ρ : Type u_3} [inst : Fintype σ] [inst_1 : Fintype ρ] (H : ℕ → σ → γ) (D : γ → ρ → Bool) (t : ℕ)
  (ε : ℝ),
  (∀ i < t, TCSlib.Cryptography.distAdv (H i) (H (i + 1)) D ≤ ε) → TCSlib.Cryptography.distAdv (H 0) (H t) D ≤ ↑t * ε
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.distAdv_fibers_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.distAdv_fibers_le : ∀ {α : Type u_1}
  {β : Type u_2} {γ : Type u_3} {ρ : Type u_4} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : Fintype ρ]
  (X Y : α → β → γ) (D : γ → ρ → Bool) (ε : ℝ),
  0 ≤ ε →
    (∀ (a : α), TCSlib.Cryptography.distAdv (X a) (Y a) D ≤ ε) →
      TCSlib.Cryptography.distAdv (fun r => X r.1 r.2) (fun r => Y r.1 r.2) D ≤ ε
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.exists_adviceReduction`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.exists_adviceReduction : ∀
  (D : Complexity.NUPPT) {rebuild : List Bool → List Bool},
  Complexity.PolyTimeComputable rebuild →
    ∀ (β : ℕ → List Bool) (b : Complexity.PolyExpr),
      (∀ (n : ℕ), (β n).length ≤ b.eval n) →
        ∃ R,
          ∃ (hcoins : R.coins = D.coins),
            ∀ (n : ℕ) (challenge : List Bool) (r : D.Coins n),
              R.distinguisherL n challenge ((Complexity.NUPPT.coinsCongr ⋯ n) r) =
                D.distinguisherL n
                  (rebuild (Turing.pairEncode (List.replicate n true) (Turing.pairEncode challenge (β n)))) r
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.reconstruction_negligible`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction.reconstruction_negligible : ∀
  {L : Complexity.PolyExpr} {G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (L.eval n) → Bool},
  TCSlib.Cryptography.SecureComputation.SliceMultiMessageSecure G →
    ∀ (D : Complexity.NUPPT) (q b : Complexity.PolyExpr) {A : ℕ → Type u_1} [(n : ℕ) → Fintype (A n)]
      [∀ (n : ℕ), Nonempty (A n)] (advice : (n : ℕ) → A n → List Bool),
      (∀ (n : ℕ) (a : A n), (advice n a).length ≤ b.eval n) →
        ∀ {rebuild : List Bool → List Bool},
          Complexity.PolyTimeComputable rebuild →
            ∀ (offset len : (n : ℕ) → A n → Fin (q.eval n + 1) → ℕ),
              (∀ (n : ℕ) (a : A n) (i : Fin (q.eval n + 1)), offset n a i + n + len n a i ≤ L.eval n) →
                ∀ (m₀ m₁ : (n : ℕ) → (a : A n) → (i : Fin (q.eval n + 1)) → Fin (len n a i) → Bool),
                  ∃ ε,
                    TCSlib.Cryptography.Negligible ε ∧
                      ∀ (n : ℕ) (a : A n),
                        TCSlib.Cryptography.distAdv
                            (fun t =>
                              rebuild
                                (Turing.pairEncode (List.replicate n true)
                                  (Turing.pairEncode
                                    (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n (q.eval n) (offset n a)
                                      (len n a) (m₀ n a) t)
                                    (advice n a))))
                            (fun t =>
                              rebuild
                                (Turing.pairEncode (List.replicate n true)
                                  (Turing.pairEncode
                                    (TCSlib.Cryptography.SecureComputation.sliceMultiEncDist G n (q.eval n) (offset n a)
                                      (len n a) (m₁ n a) t)
                                    (advice n a))))
                            (D.distinguisherL n) ≤
                          ε n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.distAdv_le_of_eq_off`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.distAdv_le_of_eq_off : ∀ {σ : Type u_1}
  {γ : Type u_2} {ρ : Type u_3} [inst : Fintype σ] [inst_1 : Fintype ρ] (X Y : σ → γ) (Bad : σ → Prop) (δ : ℝ),
  TCSlib.Cryptography.uprob Bad ≤ δ →
    (∀ (r : σ), ¬Bad r → X r = Y r) → ∀ (D : γ → ρ → Bool), TCSlib.Cryptography.distAdv X Y D ≤ δ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.statClose_of_eq_off`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.statClose_of_eq_off : ∀ {σ : Type u_1}
  {γ : Type u_2} [inst : Fintype σ] (X Y : σ → γ) (Bad : σ → Prop) (δ : ℝ),
  TCSlib.Cryptography.uprob Bad ≤ δ → (∀ (r : σ), ¬Bad r → X r = Y r) → TCSlib.Cryptography.StatClose X Y δ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord : (List Bool → List Bool) →
  (List Bool → List Bool) →
    (List Bool → ℕ) →
      (List Bool → ℕ) →
        (List Bool → ℕ) →
          (List Bool → ℕ) →
            (List Bool → List Bool) → (List Bool → List Bool) → (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith : (List Bool → List Bool) →
  ((l : ℕ) → (Fin l → Bool) → List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith_congr_at`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith_congr_at : ∀
  (args args' : List Bool → List Bool) (row row' : (l : ℕ) → (Fin l → Bool) → List Bool → List Bool) (z z' : List Bool),
  args z = args' z' →
    (∀ (l : ℕ) (a : Fin l → Bool), row l a z = row' l a z') →
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith args row z =
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith args' row' z'
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith_eq : ∀
  (args : List Bool → List Bool) (row : (l : ℕ) → (Fin l → Bool) → List Bool → List Bool) (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith args row z =
    have count := (Complexity.BinArith.decWords (args z)).length;
    have arity := min count 2;
    if count ≤ 2 then Complexity.BinArith.encWords (List.map (fun a => row arity a z) Finset.univ.toList) else []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith_of_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith_of_encoded : ∀
  (args : List Bool → List Bool) (row : (l : ℕ) → (Fin l → Bool) → List Bool → List Bool) (z : List Bool)
  (vertices : List ℕ),
  vertices.length ≤ 2 →
    args z = Complexity.BinArith.encWords (List.map (fun v => List.replicate v true) vertices) →
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith args row z =
        Complexity.BinArith.encWords (List.map (fun a => row vertices.length a z) Finset.univ.toList)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith_poly : ∀
  {args : List Bool → List Bool} (row : (l : ℕ) → (Fin l → Bool) → List Bool → List Bool),
  Complexity.PolyTimeComputable args →
    (∀ l ≤ 2, ∀ (a : Fin l → Bool), Complexity.PolyTimeComputable (row l a)) →
      Complexity.PolyTimeComputable
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWordWith args row)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_eq : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord E₁ E₂ width bound inputs gate kind args
      coins z =
    have count := (Complexity.BinArith.decWords (args z)).length;
    have arity := min count 2;
    if count ≤ 2 then
      Complexity.BinArith.encWords
        (List.map
          (fun a =>
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind
              args coins arity a z)
          Finset.univ.toList)
    else []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_garbledTable`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_garbledTable : ∀
  (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
  (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z))
  (s :
    TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
  (i : Fin C.gates.length),
  C.gates[i].args.length ≤ 2 →
    args z = Complexity.BinArith.encWords (List.map (fun v => List.replicate v true) C.gates[i].args) →
      (∀ (a : Fin C.gates[i].args.length → Bool),
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind
              args coins C.gates[i].args.length a z =
            TCSlib.Cryptography.SecureComputation.garbledRow
              (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)) C s i ((s.2.2 i) a)) →
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord E₁ E₂ width bound inputs gate
            kind args coins z =
          Complexity.BinArith.encWords
            (TCSlib.Cryptography.SecureComputation.garbledTable
              (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (width z)) C s i)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_garbledTable._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_garbledTable._proof_1 : ∀
  (inputs : List Bool → ℕ) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z)),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_garbledTable._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_garbledTable._proof_2 : ∀
  (inputs : List Bool → ℕ) (z : List Bool) (C : BoolCircuit.DAGCircuit (inputs z)) (i : Fin C.gates.length),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      ∀ {width bound inputs gate : List Bool → ℕ} {kind args coins : List Bool → List Bool},
        (Complexity.PolyTimeComputable fun z => List.replicate (width z) true) →
          (Complexity.PolyTimeComputable fun z => List.replicate (bound z) true) →
            (Complexity.PolyTimeComputable fun z => List.replicate (inputs z) true) →
              (Complexity.PolyTimeComputable fun z => List.replicate (gate z) true) →
                Complexity.PolyTimeComputable kind →
                  Complexity.PolyTimeComputable args →
                    Complexity.PolyTimeComputable coins →
                      Complexity.PolyTimeComputable
                        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins.tableWord E₁ E₂ width
                          bound inputs gate kind args coins)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (S : ℕ) → ℕ → (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) → C.size ≤ S → Type
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest C S n hA hS =
    ((Fin S → Fin 2 → Bool) ×
      ({ x // x ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding C S hS) } →
          Fin n → Bool) ×
        ({ x //
            x ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS) } →
          Fin (2 * n) → Bool))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (S n : ℕ) →
      (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
        (hS : C.size ≤ S) →
          (Fin (10 * S * n + 2 * S) → Bool) ≃
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest C S n hA hS ×
              (Fin C.size → Bool → Fin n → Bool) ×
                ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → (Fin n → Bool) × (Fin n → Bool))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (hG : C.gates.length ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r =
    have q := (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv S n) r;
    ((q.2.2, fun x => q.1 (↑x).1 (↑x).2, fun x => q.2.1 (↑x).1 (↑x).2), fun w b => q.1 b (Fin.castLE hS w), fun i a =>
      (fun t =>
        q.2.1 (Fin.castLE hG i)
          ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
              C.gates[↑i].args.length ⋯)
            a)
          ((finCongr ⋯).symm (Fin.castAdd n t)),
        fun t =>
        q.2.1 (Fin.castLE hG i)
          ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
              C.gates[↑i].args.length ⋯)
            a)
          ((finCongr ⋯).symm (Fin.natAdd n t))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_key : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).2.1 w b t =
    (List.ofFn r).getD ((b.toNat * S + ↑w) * n + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_nonce_first`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_nonce_first : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool) (t : Fin n),
  (((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).2.2 i a).1 t =
    (List.ofFn r).getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
      false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_nonce_second`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_nonce_second : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool) (t : Fin n),
  (((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).2.2 i a).2 t =
    (List.ofFn r).getD
      (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_shift`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_shift : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).1.1 i t =
    (List.ofFn r).getD (10 * S * n + 2 * ↑i + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_unused_key`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_unused_key : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool)
  (x : { x // x ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding C S hS) })
  (t : Fin n),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).1.2.1 x t =
    (List.ofFn r).getD (((↑x).1.toNat * S + ↑(↑x).2) * n + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_unused_row`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_unused_row : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool)
  (x : { x // x ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS) })
  (t : Fin (2 * n)),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).1.2.2 x t =
    (List.ofFn r).getD (2 * S * n + (4 * ↑(↑x).1 + ↑(↑x).2) * (2 * n) + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) → (S : ℕ) → C.size ≤ S → Fin C.size × Bool ↪ Bool × Fin S
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hS : C.size ≤ S) (x x_1 : Fin C.size × Bool),
  (x.2, Fin.castLE hS x.1) = (x_1.2, Fin.castLE hS x_1.1) → x = x_1
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding.congr_simp`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding.congr_simp : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hS : C.size ≤ S),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding C S hS =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding C S hS
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hS : C.size ≤ S) (w : Fin C.size) (b : Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding C S hS) (w, b) = (b, Fin.castLE hS w)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.key_not_mem_range`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.key_not_mem_range : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hS : C.size ≤ S) (w : Fin S) (b : Bool),
  C.size ≤ ↑w →
    (b, w) ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding C S hS)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.key_not_mem_range._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.key_not_mem_range._proof_1_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (w : Fin S), C.size ≤ ↑w → ∀ (w' : Fin C.size), ↑w' = ↑w → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (S n : ℕ) →
      (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
        (hS : C.size ≤ S) →
          TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest C S n hA hS →
            (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[↑i].args.length → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation_apply`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation_apply : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (hG : C.gates.length ≤ S)
  (p : TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest C S n hA hS) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool) (t : Fin C.gates[↑i].args.length),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation C S n hA hS p i) a t =
    (a t ^^ p.1 (Fin.castLE hG i) (Fin.castLE ⋯ t))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (hG : C.gates.length ≤ S)
  (p : TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest C S n hA hS) (i : Fin C.gates.length),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation C S n hA hS p i =
    TCSlib.Cryptography.xorPerm fun t => p.1 (Fin.castLE hG i) (Fin.castLE ⋯ t)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding : {m : ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (S : ℕ) →
      (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
        C.size ≤ S → (i : Fin C.gates.length) × (Fin C.gates[↑i].args.length → Bool) ↪ Fin S × Fin 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_10`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_10 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) ⦃a₁ a₂ : (i : Fin C.gates.length) × (Fin C.gates[↑i].args.length → Bool)⦄,
  (Fin.castLE ⋯ a₁.fst,
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
            C.gates[↑a₁.fst].args.length ⋯)
          a₁.snd) =
      (Fin.castLE ⋯ a₂.fst,
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
            C.gates[↑a₂.fst].args.length ⋯)
          a₂.snd) →
    a₁ = a₂
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_2 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_3 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (i : Fin C.gates.length), ¬↑i < C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_4 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_5`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_5 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (i : Fin C.gates.length), ↑i < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_6`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_6 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (x : (i : Fin C.gates.length) × (Fin C.gates[↑i].args.length → Bool)),
  ↑x.fst < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_7`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_7 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
    ∀ (x : (i : Fin C.gates.length) × (Fin C.gates[↑i].args.length → Bool)), C.gates[↑x.fst].args.length ≤ 2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_8`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_8 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) ⦃a₁ : (i : Fin C.gates.length) × (Fin C.gates[↑i].args.length → Bool)⦄,
  ↑a₁.fst < C.gates.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_9`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding._proof_9 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
    ∀ ⦃a₁ : (i : Fin C.gates.length) × (Fin C.gates[↑i].args.length → Bool)⦄, C.gates[↑a₁.fst].args.length ≤ 2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding.congr_simp`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding.congr_simp : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS) ⟨i, a⟩ =
    (Fin.castLE hG i,
      (TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding C.gates[↑i].args.length
          ⋯)
        a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (code : Fin 4),
  2 ^ C.gates[↑i].args.length ≤ ↑code →
    (Fin.castLE hG i, code) ∉
      Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code._proof_1_3 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (i : Fin C.gates.length) (code : Fin 4),
  ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code._proof_1_4 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ),
  (∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
    ∀ (i : Fin C.gates.length) (code : Fin 4) (a : Fin C.gates[↑i].args.length → Bool),
      ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code._proof_1_5`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code._proof_1_5 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (i : Fin C.gates.length) (code : Fin 4),
  2 ^ C.gates[↑i].args.length ≤ ↑code →
    ∀ (a : Fin C.gates[↑i].args.length → Bool),
      ↑((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
                C.gates[↑i].args.length ⋯)
              a) =
          ↑code →
        ↑((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
                  C.gates[↑i].args.length ⋯)
                a) <
            2 ^ C.gates[↑i].args.length →
          False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_gate`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_gate : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (i : Fin S) (a : Fin 4),
  C.gates.length ≤ ↑i →
    (i, a) ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_gate._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_gate._proof_1_3 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ) (i : Fin S), C.gates.length ≤ ↑i → ∀ (j : Fin C.gates.length), ↑j = ↑i → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_eq : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S)
  (seed :
    List Bool → TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
  (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
      (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
    (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (t : Fin n),
        ((seed q).2.1 i a).1 t =
          q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
            false) →
      (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (t : Fin n),
          ((seed q).2.1 i a).2 t =
            q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
              false) →
        (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool)
            (t : Fin C.gates[↑i].args.length),
            ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
          ∀ (r : Fin (10 * S * n + 2 * S) → Bool),
            seed (List.ofFn r) =
              (((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).2.1,
                ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).2.2,
                TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation C S n hA hS
                  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).1)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_on_inverse`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_on_inverse : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S)
  (seed :
    List Bool → TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
  (∀ (q : List Bool) (w : Fin C.size) (b : Bool) (t : Fin n),
      (seed q).1 w b t = q.getD ((b.toNat * S + ↑w) * n + ↑t) false) →
    (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (t : Fin n),
        ((seed q).2.1 i a).1 t =
          q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + ↑t)
            false) →
      (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool) (t : Fin n),
          ((seed q).2.1 i a).2 t =
            q.getD (2 * S * n + (4 * ↑i + List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)) * (2 * n) + n + ↑t)
              false) →
        (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool)
            (t : Fin C.gates[↑i].args.length),
            ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
          ∀ (p : TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest C S n hA hS)
            (d :
              (Fin C.size → Bool → Fin n → Bool) ×
                ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → (Fin n → Bool) × (Fin n → Bool))),
            seed
                (List.ofFn
                  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS).symm (p, d))) =
              (d.1, d.2, TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation C S n hA hS p)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_perm`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_perm : ∀ {m : ℕ} {ρ : Type}
  (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (seed : List Bool → TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ρ),
  (∀ (q : List Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool)
      (t : Fin C.gates[↑i].args.length), ((seed q).2.2 i) a t = (a t ^^ q.getD (10 * S * n + 2 * ↑i + ↑t) false)) →
    ∀ (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin C.gates.length) (a : Fin C.gates[↑i].args.length → Bool),
      ((seed (List.ofFn r)).2.2 i) a =
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation C S n hA hS
            ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv C S n hA hS) r).1 i)
          a
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewP_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewP_eq : ∀
  (π : TCSlib.Cryptography.Protocol) (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
            (π.viewP w zA zB r).encode =
              Turing.pairEncode (Turing.pairEncode w zA)
                (Turing.pairEncode (List.ofFn r.1)
                  (TCSlib.Cryptography.Strategy.encodeMsgs [msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))]))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewV_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewV_eq : ∀
  (π : TCSlib.Cryptography.Protocol) (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
            (π.viewV w zA zB r).encode =
              Turing.pairEncode (Turing.pairEncode w zB)
                (Turing.pairEncode (List.ofFn r.2)
                  (TCSlib.Cryptography.Strategy.encodeMsgs [msgA w zA (List.ofFn r.1)]))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outP_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outP_eq : ∀ (π : TCSlib.Cryptography.Protocol)
  (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          (∀ (w z r b : List Bool), π.P.next w z r [b] = b) →
            ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
              π.outP w zA zB r = msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outV_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outV_eq : ∀ (π : TCSlib.Cryptography.Protocol)
  (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
            π.outV π.P w zA zB r = msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realA_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realA_eq : ∀
  (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool)
  {G : TCSlib.Cryptography.SecureComputation.Functionality}
  (H : TCSlib.Cryptography.SecureComputation.HybridProtocol G),
  H.main.rounds = Complexity.PolyExpr.const 2 →
    H.main.verifierFirst = false →
      (∀ (w z r : List Bool), H.main.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), H.main.V.next w z r [a] = msgB w z r a) →
          ∀ (F : TCSlib.Cryptography.SecureComputation.Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
            (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n),
            H.realA F n x y r =
              have w := List.replicate n true;
              have zA := H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2);
              have zB := H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2);
              have a := msgA w zA (List.ofFn r.1);
              have b := msgB w zB (List.ofFn r.2) a;
              Turing.pairEncode
                (Turing.pairEncode (Turing.pairEncode w zA)
                  (Turing.pairEncode (List.ofFn r.1) (TCSlib.Cryptography.Strategy.encodeMsgs [b])))
                b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realB_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realB_eq : ∀
  (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool)
  {G : TCSlib.Cryptography.SecureComputation.Functionality}
  (H : TCSlib.Cryptography.SecureComputation.HybridProtocol G),
  H.main.rounds = Complexity.PolyExpr.const 2 →
    H.main.verifierFirst = false →
      (∀ (w z r : List Bool), H.main.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), H.main.V.next w z r [a] = msgB w z r a) →
          (∀ (w z r b : List Bool), H.main.P.next w z r [b] = b) →
            ∀ (F : TCSlib.Cryptography.SecureComputation.Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
              (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n),
              H.realB F n x y r =
                have w := List.replicate n true;
                have zA := H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2);
                have zB := H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2);
                have a := msgA w zA (List.ofFn r.1);
                have b := msgB w zB (List.ofFn r.2) a;
                Turing.pairEncode
                  (Turing.pairEncode (Turing.pairEncode w zB)
                    (Turing.pairEncode (List.ofFn r.2) (TCSlib.Cryptography.Strategy.encodeMsgs [a])))
                  b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcriptWith_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcriptWith_eq : ∀
  (π : TCSlib.Cryptography.Protocol) (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
            π.transcriptWith π.P w zA zB r =
              ([msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))], [msgA w zA (List.ofFn r.1)])
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcript_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcript_eq : ∀
  (π : TCSlib.Cryptography.Protocol) (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
            π.transcript w zA zB r =
              ([msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))], [msgA w zA (List.ofFn r.1)])
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewP_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewP_eq : ∀
  (π : TCSlib.Cryptography.Protocol) (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
            π.viewP w zA zB r =
              { x := w, z := zA, r := List.ofFn r.1,
                received := [msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))] }
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewV_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewV_eq : ∀
  (π : TCSlib.Cryptography.Protocol) (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
            π.viewV w zA zB r = { x := w, z := zB, r := List.ofFn r.2, received := [msgA w zA (List.ofFn r.1)] }
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.WordLists.ofFnTable_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.WordLists.ofFnTable_poly : ∀ {count : List Bool → ℕ}
  (f : (z : List Bool) → Fin (count z) → List Bool) (entry : List Bool → ℕ → List Bool),
  (Complexity.PolyTimeComputable fun z => List.replicate (count z) true) →
    (Complexity.PolyTimeComputable fun w => entry (Complexity.pairSndD w) (Complexity.pairFstD w).length) →
      (∀ (z : List Bool) (i : Fin (count z)), f z i = entry z ↑i) →
        Complexity.PolyTimeComputable fun z => Complexity.BinArith.encWords (List.ofFn (f z))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.WordLists.rangeTable_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.WordLists.rangeTable_poly : ∀ {count : List Bool → ℕ}
  {entry : List Bool → ℕ → List Bool},
  (Complexity.PolyTimeComputable fun z => List.replicate (count z) true) →
    (Complexity.PolyTimeComputable fun w => entry (Complexity.pairSndD w) (Complexity.pairFstD w).length) →
      Complexity.PolyTimeComputable fun z => Complexity.BinArith.encWords (List.map (entry z) (List.range (count z)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.acceptProb_firstTape`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.acceptProb_firstTape : ∀
  {G : TCSlib.Cryptography.SecureComputation.Functionality} (H : TCSlib.Cryptography.SecureComputation.HybridProtocol G)
  (n m : ℕ) (hLen : H.main.P.coinLen (List.replicate n true).length = m) (X : H.Coins n → List Bool)
  (Y : (Fin m → Bool) → List Bool),
  (∀ (r : H.Coins n),
      X r =
        Y
          ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv H.main.P
              (List.replicate n true).length m hLen)
            r.1)) →
    ∀ {ρ : Type u_1} [inst : Fintype ρ] (D : List Bool → ρ → Bool),
      TCSlib.Cryptography.acceptProb X D = TCSlib.Cryptography.acceptProb Y D
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.aliceMessageBound`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.aliceMessageBound : Complexity.PolyExpr →
  Complexity.PolyExpr → Complexity.PolyExpr → Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.aliceMessageBound.eq_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.aliceMessageBound.eq_1 : ∀ (S A O : Complexity.PolyExpr),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.aliceMessageBound S A O =
    ((((Complexity.PolyExpr.const 2).mul
                  (S.mul
                    (((Complexity.PolyExpr.const 112).mul Complexity.PolyExpr.var).add
                      (Complexity.PolyExpr.const 82)))).add
              ((Complexity.PolyExpr.const 2).mul
                (A.mul
                  (((Complexity.PolyExpr.const 2).mul Complexity.PolyExpr.var).add (Complexity.PolyExpr.const 2))))).add
          (O.mul (((Complexity.PolyExpr.const 6).mul Complexity.PolyExpr.var).add (Complexity.PolyExpr.const 6)))).add
      (Complexity.PolyExpr.const 4)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.aliceMessageBound_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.aliceMessageBound_eq : ∀ (S A O : Complexity.PolyExpr)
  (n : ℕ),
  (TCSlib.Cryptography.SecureComputation.YaoHybridProof.aliceMessageBound S A O).eval n =
    2 * (S.eval n * (112 * n + 82)) + 2 * (A.eval n * (2 * n + 2)) + O.eval n * (6 * n + 6) + 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode_encoded : ∀ (N : List Bool)
  (vs : List (Fin N.length → Bool)) (args : List ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode
      (Turing.pairEncode N
        (Turing.pairEncode (Complexity.BinArith.encWords (List.map List.ofFn vs))
          (Complexity.BinArith.encWords (List.map (fun a => List.replicate a true) args)))) =
    Complexity.BinArith.encWords (List.map List.ofFn (List.map (fun a => vs.getD a default) args))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode z =
    Complexity.BinArith.mapW TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup
      (Turing.pairEncode (Turing.pairEncode (Complexity.pairFstD z) (Complexity.pairFstD (Complexity.pairSndD z)))
        (Complexity.pairSndD (Complexity.pairSndD z)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode_poly : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged_eq : ∀ (F : List Bool → List Bool)
  (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged F w = if w = [] then [] else F (List.drop 1 w)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged_option`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged_option : ∀ (F : List Bool → List Bool)
  (o : Option (List Bool)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged F
      (match o with
      | none => []
      | some m => true :: m) =
    match o with
    | none => []
    | some m => F m
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged_poly : ∀ {F : List Bool → List Bool},
  Complexity.PolyTimeComputable F →
    Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.bindTagged F)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged z =
    if Complexity.pairSndD z = [] then []
    else
      if (List.drop 1 (Complexity.pairSndD z)).length = (Complexity.pairFstD z).length then
        true :: List.drop 1 (Complexity.pairSndD z)
      else []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option : ∀ (N : List Bool)
  (o : Option (List Bool)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged
      (Turing.pairEncode N
        (match o with
        | none => []
        | some m => true :: m)) =
    match o.bind (TCSlib.Cryptography.decodeFin N.length) with
    | none => []
    | some k => true :: List.ofFn k
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option.match_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option.match_1 : (N : List Bool) →
  (motive : Option (Fin N.length → Bool) → Sort u_1) →
    (x : Option (Fin N.length → Bool)) → (Unit → motive none) → ((k : Fin N.length → Bool) → motive (some k)) → motive x
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_poly : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.encodeMsgs_eq_encWords`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.encodeMsgs_eq_encWords : ∀ (L : List (List Bool)),
  TCSlib.Cryptography.Strategy.encodeMsgs L = Complexity.BinArith.encWords L
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord : (List Bool → List Bool) →
  (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord_encoded : ∀
  (E₁ E₂ : List Bool → List Bool) (N : List Bool) (T : ℕ → List (List Bool)) (v : ℕ) (g : BoolCircuit.DAGGate)
  (vs : List (Fin N.length → Bool)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord E₁ E₂
      (Turing.pairEncode N
        (Turing.pairEncode (Complexity.BinArith.encWords (List.map (fun a => List.replicate a true) g.args))
          (Turing.pairEncode (Complexity.BinArith.encWords (List.map List.ofFn vs))
            (Complexity.BinArith.encWords (T v))))) =
    Complexity.BinArith.encWords
      (List.map List.ofFn
        (vs ++
          [TCSlib.Cryptography.SecureComputation.evalGate
              (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ N.length) T v g vs]))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord_eq : ∀ (E₁ E₂ : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord E₁ E₂ z =
    Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD z)) ++
      Turing.pairEncode (TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord E₁ E₂ z) []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord_poly : ∀
  {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord E₁ E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord : (List Bool → List Bool) →
  (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord_encoded : ∀ (E₁ E₂ : List Bool → List Bool)
  (N : List Bool) (T : ℕ → List (List Bool)) (v : ℕ) (g : BoolCircuit.DAGGate) (vs : List (Fin N.length → Bool)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord E₁ E₂
      (Turing.pairEncode N
        (Turing.pairEncode (Complexity.BinArith.encWords (List.map (fun a => List.replicate a true) g.args))
          (Turing.pairEncode (Complexity.BinArith.encWords (List.map List.ofFn vs))
            (Complexity.BinArith.encWords (T v))))) =
    List.ofFn
      (TCSlib.Cryptography.SecureComputation.evalGate
        (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ N.length) T v g vs)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord_eq : ∀ (E₁ E₂ : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord E₁ E₂ z =
    have N := Complexity.pairFstD z;
    have args := Complexity.pairFstD (Complexity.pairSndD z);
    have values := Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD z));
    have rows := Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD z));
    have keys :=
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.argKeysCode
        (Turing.pairEncode N (Turing.pairEncode values args));
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault
      (Turing.pairEncode N
        (TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged
          (TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged E₁ E₂)
          (Turing.pairEncode (Turing.pairEncode N keys) rows)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord_poly : ∀ {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateWord E₁ E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded : ∀ {β : Type}
  (F : List Bool → List Bool) (q : List Bool) (rows : List (List Bool)) (f : List Bool → Option β)
  (payload : β → List Bool),
  (∀ (row : List Bool),
      F (Turing.pairEncode q row) =
        match f row with
        | none => []
        | some b => true :: payload b) →
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged F
        (Turing.pairEncode q (Complexity.BinArith.encWords rows)) =
      match List.findSome? f rows with
      | none => []
      | some b => true :: payload b
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded._proof_1_1 : ∀
  (pre post : List (List Bool)), ¬pre.length < pre.length + (post.length + 1) → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded._proof_1_2 : ∀
  (F : List Bool → List Bool) (q : List Bool) (pre : List (List Bool)) (row : List Bool) (post : List (List Bool)),
  pre.length + (post.length + 1) ≤ pre.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded.match_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded.match_1 : {β : Type} →
  (motive : Option β → Sort u_1) → (x : Option β) → (Unit → motive none) → ((b : β) → motive (some b)) → motive x
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_eq : ∀ (F : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged F z =
    have rows := Complexity.BinArith.decWords (Complexity.pairSndD z);
    have i :=
      TCSlib.Cryptography.EncodingMachines.firstIdx
        (fun j => !decide (F (Turing.pairEncode (Complexity.pairFstD z) (rows.getD j [])) = [])) rows.length;
    if rows.length ≤ i then [] else F (Turing.pairEncode (Complexity.pairFstD z) (rows.getD i []))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_poly : ∀ {F : List Bool → List Bool},
  Complexity.PolyTimeComputable F →
    Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged F)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstThenEcho_efficient`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstThenEcho_efficient : ∀
  (S : TCSlib.Cryptography.Strategy) (first : List Bool → List Bool → List Bool → List Bool),
  (∀ (x z r : List Bool), S.next x z r [] = first x z r) →
    (∀ (x z r a : List Bool) (hist : List (List Bool)), S.next x z r (a :: hist) = a) →
      (Complexity.PolyTimeComputable fun w =>
          first (TCSlib.Cryptography.GI.argX w) (TCSlib.Cryptography.GI.argZ w) (Complexity.NUPPT.inCoins w)) →
        S.Efficient
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstThenEcho_efficient._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstThenEcho_efficient._simp_1_1 : ∀ (x y : List Bool),
  (Turing.pairEncode x y = []) = False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledRunWith_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledRunWith_poly : ∀
  {E₁ E₂ N tableWord : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      Complexity.PolyTimeComputable N →
        ∀ (gateCode : BoolCircuit.DAGGate → List Bool) (gs : List Bool → List BoolCircuit.DAGGate)
          (init : (x : List Bool) → List (Fin (N x).length → Bool)) (T : List Bool → ℕ → List (List Bool)),
          (Complexity.PolyTimeComputable fun x => Complexity.BinArith.encWords (List.map gateCode (gs x))) →
            (Complexity.PolyTimeComputable fun x => Complexity.BinArith.encWords (List.map List.ofFn (init x))) →
              Complexity.PolyTimeComputable tableWord →
                (∀ (g : BoolCircuit.DAGGate),
                    Complexity.pairSndD (gateCode g) =
                      Complexity.BinArith.encWords (List.map (fun a => List.replicate a true) g.args)) →
                  (∀ (x : List Bool) (g : BoolCircuit.DAGGate) (vs : List (Fin (N x).length → Bool)),
                      tableWord
                          (Turing.pairEncode x
                            (Turing.pairEncode (gateCode g) (Complexity.BinArith.encWords (List.map List.ofFn vs)))) =
                        Complexity.BinArith.encWords (T x vs.length)) →
                    Complexity.PolyTimeComputable fun x =>
                      Complexity.BinArith.encWords
                        (List.map List.ofFn
                          (BoolCircuit.runWith
                            (fun g vs =>
                              TCSlib.Cryptography.SecureComputation.evalGate
                                (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (N x).length) (T x) vs.length
                                g vs)
                            (gs x) (init x)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledRunWith_poly._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledRunWith_poly._proof_1_1 : ∀
  {E₁ E₂ : List Bool → List Bool} {N : List Bool → List Bool} (gateCode : BoolCircuit.DAGGate → List Bool)
  (gs : List Bool → List BoolCircuit.DAGGate) (init : (x : List Bool) → List (Fin (N x).length → Bool))
  (T : List Bool → ℕ → List (List Bool)) (Cg cg Ci ci Cn cn : ℕ) (x : List Bool) (i : ℕ),
  (N x).length ≤ (Complexity.PolyExpr.normal Cn cn).eval x.length →
    ¬2 * (N x).length + 2 ≤ 2 * (Complexity.PolyExpr.normal Cn cn).eval x.length + 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledRunWith_poly._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledRunWith_poly._proof_1_2 : ∀
  {E₁ E₂ N : List Bool → List Bool} (gateCode : BoolCircuit.DAGGate → List Bool)
  (gs : List Bool → List BoolCircuit.DAGGate) (init : (x : List Bool) → List (Fin (N x).length → Bool))
  (T : List Bool → ℕ → List (List Bool)) (Cg cg Ci ci Cn cn : ℕ) (x : List Bool) (i : ℕ),
  (Complexity.BinArith.encWords (List.map gateCode (List.drop i (gs x)))).length ≤
      (Complexity.PolyExpr.normal Cg cg).eval x.length →
    (Complexity.BinArith.encWords
            (List.map List.ofFn
              (BoolCircuit.runWith
                (fun g vs =>
                  TCSlib.Cryptography.SecureComputation.evalGate
                    (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (N x).length) (T x) vs.length g vs)
                (List.take i (gs x)) (init x)))).length ≤
        ((Complexity.PolyExpr.normal Ci ci).eval x.length + (Complexity.PolyExpr.normal Cg cg).eval x.length) *
          (2 * (Complexity.PolyExpr.normal Cn cn).eval x.length + 2) →
      ¬2 * (Complexity.BinArith.encWords (List.map gateCode (List.drop i (gs x)))).length + 2 +
              (Complexity.BinArith.encWords
                  (List.map List.ofFn
                    (BoolCircuit.runWith
                      (fun g vs =>
                        TCSlib.Cryptography.SecureComputation.evalGate
                          (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ (N x).length) (T x) vs.length g vs)
                      (List.take i (gs x)) (init x)))).length ≤
            2 * (Complexity.PolyExpr.normal Cg cg).eval x.length +
              (2 +
                ((Complexity.PolyExpr.normal Ci ci).eval x.length + (Complexity.PolyExpr.normal Cg cg).eval x.length) *
                  (2 * (Complexity.PolyExpr.normal Cn cn).eval x.length + 2)) →
        False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledStep`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledStep : (List Bool → List Bool) →
  (List Bool → List Bool) → (List Bool → List Bool) → (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledStep_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledStep_eq : ∀
  (E₁ E₂ N tableWord : List Bool → List Bool) (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledStep E₁ E₂ N tableWord w =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.evalGateAppendWord E₁ E₂
      (Turing.pairEncode (N (Complexity.pairFstD w))
        (Turing.pairEncode (Complexity.pairSndD (Complexity.pairFstD (Complexity.pairSndD w)))
          (Turing.pairEncode (Complexity.pairSndD (Complexity.pairSndD w)) (tableWord w))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledStep_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledStep_poly : ∀
  {E₁ E₂ N tableWord : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      Complexity.PolyTimeComputable N →
        Complexity.PolyTimeComputable tableWord →
          Complexity.PolyTimeComputable
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledStep E₁ E₂ N tableWord)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup_encoded : ∀ (N : List Bool)
  (vs : List (Fin N.length → Bool)) (a : ℕ),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup
      (Turing.pairEncode (Turing.pairEncode N (Complexity.BinArith.encWords (List.map List.ofFn vs)))
        (List.replicate a true)) =
    List.ofFn (vs.getD a default)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup z =
    TCSlib.Cryptography.EnsembleLemmas.padL (Complexity.pairFstD (Complexity.pairFstD z)).length
      (Complexity.BinArith.getW
        (Turing.pairEncode (Complexity.pairSndD z) (Complexity.pairSndD (Complexity.pairFstD z))))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup_poly : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.keyLookup
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTable_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTable_le : ∀
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) {m : ℕ} (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (i : Fin C.gates.length),
  C.gates[i].args.length ≤ 2 →
    (TCSlib.Cryptography.Strategy.encodeMsgs
          (TCSlib.Cryptography.SecureComputation.garbledTable
            (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C s i)).length ≤
      56 * n + 40
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTable_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTable_le._proof_1_1 : ∀ (n : ℕ)
  {m : ℕ} (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ¬4 * (2 * (7 * n + 4) + 2) = 56 * n + 40 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTables_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTables_le : ∀
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) {m : ℕ} (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
  (∀ (i : Fin C.gates.length), C.gates[i].args.length ≤ 2) →
    (TCSlib.Cryptography.Strategy.encodeMsgs
          (List.ofFn fun i =>
            TCSlib.Cryptography.Strategy.encodeMsgs
              (TCSlib.Cryptography.SecureComputation.garbledTable
                (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C s i))).length ≤
      C.gates.length * (112 * n + 82)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTables_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTables_le._proof_1_1 : ∀
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) {m : ℕ} (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))),
  ¬2 * (56 * n + 40) + 2 = 112 * n + 82 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_keys_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_keys_le : ∀ {a n : ℕ}
  (keys : Fin a → Fin n → Bool),
  (TCSlib.Cryptography.Strategy.encodeMsgs (List.ofFn fun i => List.ofFn (keys i))).length ≤ a * (2 * n + 2)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le : ∀ {o n : ℕ}
  (keys : Fin o → Bool → Fin n → Bool),
  (TCSlib.Cryptography.Strategy.encodeMsgs
        (List.ofFn fun j => Turing.pairEncode (List.ofFn (keys j false)) (List.ofFn (keys j true)))).length ≤
    o * (6 * n + 6)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le._proof_1_1 : ∀ {n : ℕ},
  ¬2 * n + 2 + n ≤ 3 * n + 2 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le._proof_1_2 : ∀ {o n : ℕ}
  (keys : Fin o → Bool → Fin n → Bool), ¬2 * (3 * n + 2) + 2 = 6 * n + 6 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledRow_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledRow_le : ∀ (E₁ E₂ : List Bool → List Bool)
  (n : ℕ) {m : ℕ} (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (i : Fin C.gates.length) (a : Fin C.gates[i].args.length → Bool),
  (TCSlib.Cryptography.SecureComputation.garbledRow (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) C s i
        a).length ≤
    7 * n + 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledRow_le._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledRow_le._proof_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledTable_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledTable_le : ∀ {K W ρ : Type}
  [inst : Inhabited K] {m : ℕ} (M : TCSlib.Cryptography.SecureComputation.MultiEnc K W ρ) (C : BoolCircuit.DAGCircuit m)
  (s : TCSlib.Cryptography.SecureComputation.GarbleSeed C K ρ) (i : Fin C.gates.length),
  C.gates[i].args.length ≤ 2 → (TCSlib.Cryptography.SecureComputation.garbledTable M C s i).length ≤ 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledTable_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledTable_le._proof_1_1 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (i : Fin C.gates.length), ¬C.gates.length ≤ C.gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_message_of_parts_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_message_of_parts_le : ∀
  (tables keys pairs : List Bool) (g a o n : ℕ),
  tables.length ≤ g * (112 * n + 82) →
    keys.length ≤ a * (2 * n + 2) →
      pairs.length ≤ o * (6 * n + 6) →
        (Turing.pairEncode tables (Turing.pairEncode keys pairs)).length ≤
          2 * (g * (112 * n + 82)) + 2 * (a * (2 * n + 2)) + o * (6 * n + 6) + 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_message_of_parts_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_message_of_parts_le._proof_1_1 : ∀
  (tables keys pairs : List Bool) (g a o n : ℕ),
  tables.length ≤ g * (112 * n + 82) →
    keys.length ≤ a * (2 * n + 2) →
      pairs.length ≤ o * (6 * n + 6) →
        ¬2 * tables.length + 2 + (2 * keys.length + 2 + pairs.length) ≤
              2 * (g * (112 * n + 82)) + 2 * (a * (2 * n + 2)) + o * (6 * n + 6) + 4 →
          False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le : ∀
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool)
  (r : (Fin n → Bool) × (Fin n → Bool)),
  ((TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).enc ks o r).length ≤ 7 * n + 4
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le._proof_1_3 : ∀ (n : ℕ),
  ¬n ≤ 7 * n + 4 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le._proof_1_4 : ∀
  (E₁ : List Bool → List Bool) (n : ℕ) (o : Fin n → Bool) (r : (Fin n → Bool) × (Fin n → Bool)) (k : Fin n → Bool),
  (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1)).length ≤
      3 * n + n + 2 →
    ¬(TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1)).length ≤
          7 * n + 4 →
      False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le._proof_1_5`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le._proof_1_5 : ∀
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (o : Fin n → Bool) (r : (Fin n → Bool) × (Fin n → Bool))
  (k₁ k₂ : Fin n → Bool),
  (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)).length ≤
      3 * n + n + 2 →
    (TCSlib.Cryptography.SecureComputation.spEncStr E₂ (List.ofFn k₁)
            (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2))
            (List.ofFn r.1)).length ≤
        3 * n +
            (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)).length +
          2 →
      ¬(TCSlib.Cryptography.SecureComputation.spEncStr E₂ (List.ofFn k₁)
                (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2))
                (List.ofFn r.1)).length ≤
            7 * n + 4 →
        False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le._proof_1_6`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le._proof_1_6 : ∀ (n : ℕ),
  ¬0 ≤ 7 * n + 4 → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le.match_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le.match_1_1 : ∀ (n : ℕ)
  (motive : List (Fin n → Bool) → Prop) (ks : List (Fin n → Bool)),
  (∀ (a : Unit), motive []) →
    (∀ (k : Fin n → Bool), motive [k]) →
      (∀ (k₁ k₂ : Fin n → Bool), motive [k₁, k₂]) →
        (∀ (head head_1 head_2 : Fin n → Bool) (tail : List (Fin n → Bool)),
            motive (head :: head_1 :: head_2 :: tail)) →
          motive ks
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_spEncStr_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_spEncStr_le : ∀ (E : List Bool → List Bool)
  (k m r : List Bool), (TCSlib.Cryptography.SecureComputation.spEncStr E k m r).length ≤ 3 * r.length + m.length + 2
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_spEncStr_le._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_spEncStr_le._proof_1_1 : ∀
  (E : List Bool → List Bool) (k m r : List Bool),
  ¬2 * r.length + 2 +
          (min r.length (E (Turing.pairEncode k r)).length +
            min m.length (List.drop r.length (E (Turing.pairEncode k r))).length) ≤
        3 * r.length + m.length + 2 →
    False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged : (List Bool → List Bool) →
  (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_encoded : ∀ (E₁ E₂ : List Bool → List Bool)
  (N : List Bool) (ks : List (Fin N.length → Bool)) (c : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged E₁ E₂
      (Turing.pairEncode N (Turing.pairEncode (Complexity.BinArith.encWords (List.map List.ofFn ks)) c)) =
    match (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ N.length).dec ks c with
    | none => []
    | some k => true :: List.ofFn k
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_encoded._simp_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_encoded._simp_1_2 : ∀ (x y : List Bool),
  (Turing.pairEncode x y = []) = False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_encoded._simp_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_encoded._simp_1_4 : ∀ {α : Type u_1}
  (a : α) (l : List α), (a :: l = []) = False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_eq : ∀ (E₁ E₂ : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged E₁ E₂ z =
    have N := Complexity.pairFstD z;
    have keys := Complexity.pairFstD (Complexity.pairSndD z);
    have c := Complexity.pairSndD (Complexity.pairSndD z);
    if keys = [] then
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged (Turing.pairEncode N (true :: c))
    else
      if Complexity.pairSndD keys = [] then
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged
          (Turing.pairEncode N
            (TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged E₁
              (Turing.pairEncode N (Turing.pairEncode N (Turing.pairEncode (Complexity.pairFstD keys) c)))))
      else
        if Complexity.pairSndD (Complexity.pairSndD keys) = [] then
          have outer :=
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged E₂
              (Turing.pairEncode N
                (Turing.pairEncode (List.replicate (TCSlib.Cryptography.SecureComputation.innerLen.eval N.length) true)
                  (Turing.pairEncode (Complexity.pairFstD keys) c)));
          if outer = [] then []
          else
            TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged
              (Turing.pairEncode N
                (TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged E₁
                  (Turing.pairEncode N
                    (Turing.pairEncode N
                      (Turing.pairEncode (Complexity.pairFstD (Complexity.pairSndD keys)) (List.drop 1 outer))))))
        else []
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged_poly : ∀ {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged E₁ E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged : (List Bool → List Bool) →
  (List Bool → List Bool) → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged_eq : ∀ (E₁ E₂ : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged E₁ E₂ z =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedDecTagged E₁ E₂
      (Turing.pairEncode (Complexity.pairFstD (Complexity.pairFstD z))
        (Turing.pairEncode (Complexity.pairSndD (Complexity.pairFstD z)) (Complexity.pairSndD z)))
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged_poly : ∀ {E₁ E₂ : List Bool → List Bool},
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.nestedRowTagged E₁ E₂)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.polyTimeComputable_reencodeWords`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.polyTimeComputable_reencodeWords : Complexity.PolyTimeComputable
  fun w => Complexity.BinArith.encWords (Complexity.BinArith.decWords w)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.polyTimeComputable_window`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.polyTimeComputable_window : ∀ {w : List Bool → List Bool}
  {off len : List Bool → ℕ},
  Complexity.PolyTimeComputable w →
    (Complexity.PolyTimeComputable fun z => List.replicate (off z) true) →
      (Complexity.PolyTimeComputable fun z => List.replicate (len z) true) →
        Complexity.PolyTimeComputable fun z => List.ofFn fun t => (w z).getD (off z + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.polyTimeComputable_window._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.polyTimeComputable_window._simp_1_1 : ∀ (k : ℕ)
  (a : List Bool), TCSlib.Cryptography.EnsembleLemmas.padL k a = List.ofFn (TCSlib.Cryptography.padFin k a)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.realB_output_switch`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.realB_output_switch : ∀
  {G : TCSlib.Cryptography.SecureComputation.Functionality} (H : TCSlib.Cryptography.SecureComputation.HybridProtocol G)
  (F : TCSlib.Cryptography.SecureComputation.Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
  (y : Fin (F.inB.eval n) → Bool) (Bad : H.Coins n → Prop) (δ : ℝ),
  TCSlib.Cryptography.uprob Bad ≤ δ →
    (∀ (r : H.Coins n),
        ¬Bad r →
          H.main.outP (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
              (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r =
            List.ofFn (F.f n x y).1) →
      TCSlib.Cryptography.StatClose (H.realB F n x y)
        (fun r =>
          Turing.pairEncode
            (H.main.viewV (List.replicate n true)
                (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
                (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
            (List.ofFn (F.f n x y).1))
        δ
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.reply_efficient`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.reply_efficient : ∀ (S : TCSlib.Cryptography.Strategy)
  (reply : List Bool → List Bool → List Bool → List Bool),
  (∀ (x z r : List Bool) (hist : List (List Bool)), S.next x z r hist = reply x z (hist.headD [])) →
    (Complexity.PolyTimeComputable fun w =>
        reply (TCSlib.Cryptography.GI.argX w) (TCSlib.Cryptography.GI.argZ w)
          (Complexity.pairFstD (TCSlib.Cryptography.GI.argM w))) →
      S.Efficient
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.simulators_of_output_switch`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.simulators_of_output_switch : ∀
  {G : TCSlib.Cryptography.SecureComputation.Functionality} (H : TCSlib.Cryptography.SecureComputation.HybridProtocol G)
  (F : TCSlib.Cryptography.SecureComputation.Functionality) (SA SB : Complexity.NUPPT)
  (switched : (n : ℕ) → (Fin (F.inA.eval n) → Bool) → (Fin (F.inB.eval n) → Bool) → H.Coins n → List Bool) (δ : ℕ → ℝ),
  TCSlib.Cryptography.Negligible δ →
    (∀ (D : Complexity.NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
        TCSlib.Cryptography.distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ δ n) →
      (∀ (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
          TCSlib.Cryptography.StatClose (H.realB F n x y) (switched n x y) (δ n)) →
        (∀ (D : Complexity.NUPPT),
            ∃ μ,
              TCSlib.Cryptography.Negligible μ ∧
                ∀ (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
                  TCSlib.Cryptography.distAdv (switched n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ μ n) →
          ∀ (D : Complexity.NUPPT),
            ∃ ε,
              TCSlib.Cryptography.Negligible ε ∧
                ∀ (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
                  TCSlib.Cryptography.distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
                    TCSlib.Cryptography.distAdv (H.realB F n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged : (List Bool → List Bool) →
  List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged.match_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged.match_1 : (motive :
    Option (List Bool) → Sort u_1) →
  (x : Option (List Bool)) → (Unit → motive none) → ((m : List Bool) → motive (some m)) → motive x
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged_eq : ∀ (E : List Bool → List Bool)
  (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged E z =
    match
      TCSlib.Cryptography.SecureComputation.spDecStr E (Complexity.pairFstD z).length
        (Complexity.pairFstD (Complexity.pairSndD z)).length
        (Complexity.pairFstD (Complexity.pairSndD (Complexity.pairSndD z)))
        (Complexity.pairSndD (Complexity.pairSndD (Complexity.pairSndD z))) with
    | none => []
    | some m => true :: m
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged_pairEncode`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged_pairEncode : ∀ (E : List Bool → List Bool)
  (N L k c : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged E
      (Turing.pairEncode N (Turing.pairEncode L (Turing.pairEncode k c))) =
    match TCSlib.Cryptography.SecureComputation.spDecStr E N.length L.length k c with
    | none => []
    | some m => true :: m
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged_poly : ∀ {E : List Bool → List Bool},
  Complexity.PolyTimeComputable E →
    Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged E)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged_poly._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged_poly._simp_1_1 : ∀ (p q : Prop)
  [dpq : Decidable (p ∧ q)] [dp : Decidable p] [dq : Decidable q], (decide p && decide q) = decide (p ∧ q)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv : (S : TCSlib.Cryptography.Strategy) →
  (n m : ℕ) → S.coinLen n = m → S.Coins n ≃ (Fin m → Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv.congr_simp`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv.congr_simp : ∀
  (S : TCSlib.Cryptography.Strategy) (n m : ℕ) (h : S.coinLen n = m),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv S n m h =
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv S n m h
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv_eq : ∀ (S : TCSlib.Cryptography.Strategy)
  (n m : ℕ) (h : S.coinLen n = m),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv S n m h =
    (finCongr h).arrowCongr (Equiv.refl Bool)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv_ofFn`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv_ofFn : ∀
  (S : TCSlib.Cryptography.Strategy) (n m : ℕ) (h : S.coinLen n = m) (r : S.Coins n),
  List.ofFn ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.strategyTapeEquiv S n m h) r) = List.ofFn r
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le : ∀
  (π : TCSlib.Cryptography.Protocol) (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool),
  π.rounds = Complexity.PolyExpr.const 2 →
    π.verifierFirst = false →
      (∀ (w z r : List Bool), π.P.next w z r [] = msgA w z r) →
        (∀ (w z r a : List Bool), π.V.next w z r [a] = msgB w z r a) →
          ∀ (BA BB : Complexity.PolyExpr),
            (∀ (w z r : List Bool), (msgA w z r).length ≤ BA.eval w.length) →
              (∀ (w z r a : List Bool), (msgB w z r a).length ≤ BB.eval w.length) →
                ∀ (w zA zB : List Bool) (r : π.ExecCoins π.P w),
                  ∀ msg ∈ (π.transcript w zA zB r).1 ++ (π.transcript w zA zB r).2,
                    msg.length ≤ (BA.add BB).eval w.length
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le._proof_1_3`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le._proof_1_3 : ∀
  (BA BB : Complexity.PolyExpr) (w : List Bool), ¬BB.eval w.length ≤ BA.eval w.length + BB.eval w.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le._proof_1_4`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le._proof_1_4 : ∀
  (BA BB : Complexity.PolyExpr) (w : List Bool), ¬BA.eval w.length ≤ BA.eval w.length + BB.eval w.length → False
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le._simp_1_1 : ∀ {α : Type u_1}
  {a : α} {s t : List α}, (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le._simp_1_2`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.twoMove_message_length_le._simp_1_2 : ∀ {α : Type u_1}
  {a b : α}, (a ∈ [b]) = (a = b)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault : List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault_encoded`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault_encoded : ∀ (N : List Bool)
  (o : Option (Fin N.length → Bool)),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault
      (Turing.pairEncode N
        (match o with
        | none => []
        | some k => true :: List.ofFn k)) =
    List.ofFn (o.getD default)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault_encoded.match_1`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault_encoded.match_1 : (N : List Bool) →
  (motive : Option (Fin N.length → Bool) → Sort u_1) →
    (o : Option (Fin N.length → Bool)) → (Unit → motive none) → ((k : Fin N.length → Bool) → motive (some k)) → motive o
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault_eq`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault_eq : ∀ (z : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault z =
    if Complexity.pairSndD z = [] then List.replicate (Complexity.pairFstD z).length false
    else List.drop 1 (Complexity.pairSndD z)
```

## `TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault_poly`

```lean
TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault_poly : Complexity.PolyTimeComputable
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.untagDefault
```

## `TCSlib.Cryptography.SecureComputation.assignIdx`

```lean
TCSlib.Cryptography.SecureComputation.assignIdx : {len : ℕ} → (Fin len → Bool) → ℕ
```

## `TCSlib.Cryptography.SecureComputation.assignIdx_eq`

```lean
TCSlib.Cryptography.SecureComputation.assignIdx_eq : ∀ {len : ℕ} (a : Fin len → Bool),
  TCSlib.Cryptography.SecureComputation.assignIdx a = List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)
```

## `TCSlib.Cryptography.SecureComputation.decodeMsgs`

```lean
TCSlib.Cryptography.SecureComputation.decodeMsgs : List Bool → List (List Bool)
```

## `TCSlib.Cryptography.SecureComputation.decodeMsgs_encodeMsgs`

```lean
TCSlib.Cryptography.SecureComputation.decodeMsgs_encodeMsgs : ∀ (l : List (List Bool)),
  TCSlib.Cryptography.SecureComputation.decodeMsgs (TCSlib.Cryptography.Strategy.encodeMsgs l) = l
```

## `TCSlib.Cryptography.SecureComputation.decodeMsgs_eq`

```lean
TCSlib.Cryptography.SecureComputation.decodeMsgs_eq : ∀ (w : List Bool),
  TCSlib.Cryptography.SecureComputation.decodeMsgs w =
    if w = [] then []
    else Complexity.pairFstD w :: TCSlib.Cryptography.SecureComputation.decodeMsgs (Complexity.pairSndD w)
```

## `TCSlib.Cryptography.SecureComputation.decodeMsgs_nil`

```lean
TCSlib.Cryptography.SecureComputation.decodeMsgs_nil : TCSlib.Cryptography.SecureComputation.decodeMsgs [] = []
```

## `TCSlib.Cryptography.SecureComputation.decodeOut`

```lean
TCSlib.Cryptography.SecureComputation.decodeOut : List Bool → List Bool → Bool
```

## `TCSlib.Cryptography.SecureComputation.decodeOut.eq_1`

```lean
TCSlib.Cryptography.SecureComputation.decodeOut.eq_1 : ∀ (k p : List Bool),
  TCSlib.Cryptography.SecureComputation.decodeOut k p =
    if k = Complexity.pairFstD p then false else decide (k = Complexity.pairSndD p)
```

## `TCSlib.Cryptography.SecureComputation.decodeOut_eq`

```lean
TCSlib.Cryptography.SecureComputation.decodeOut_eq : ∀ (k p : List Bool),
  TCSlib.Cryptography.SecureComputation.decodeOut k p =
    if k = Complexity.pairFstD p then false else decide (k = Complexity.pairSndD p)
```

## `TCSlib.Cryptography.SecureComputation.decodeOut_fst`

```lean
TCSlib.Cryptography.SecureComputation.decodeOut_fst : ∀ (k₀ k₁ : List Bool),
  TCSlib.Cryptography.SecureComputation.decodeOut k₀ (Turing.pairEncode k₀ k₁) = false
```

## `TCSlib.Cryptography.SecureComputation.decodeOut_snd`

```lean
TCSlib.Cryptography.SecureComputation.decodeOut_snd : ∀ (k₀ k₁ : List Bool),
  k₁ ≠ k₀ → TCSlib.Cryptography.SecureComputation.decodeOut k₁ (Turing.pairEncode k₀ k₁) = true
```

## `TCSlib.Cryptography.SecureComputation.encodeCircuit`

```lean
TCSlib.Cryptography.SecureComputation.encodeCircuit : {m k : ℕ} →
  BoolCircuit.DAGCircuit m → (Fin k → ℕ) → List Bool
```

## `TCSlib.Cryptography.SecureComputation.encodeCircuit_eq`

```lean
TCSlib.Cryptography.SecureComputation.encodeCircuit_eq : ∀ {m k : ℕ} (C : BoolCircuit.DAGCircuit m)
  (outs : Fin k → ℕ),
  TCSlib.Cryptography.SecureComputation.encodeCircuit C outs =
    Turing.pairEncode C.encode
      (TCSlib.Cryptography.Strategy.encodeMsgs (List.ofFn fun j => BoolCircuit.encodeNat (outs j)))
```

## `TCSlib.Cryptography.SecureComputation.encodeCircuit_injective`

```lean
TCSlib.Cryptography.SecureComputation.encodeCircuit_injective : ∀ {m k : ℕ} {C C' : BoolCircuit.DAGCircuit m}
  {outs outs' : Fin k → ℕ},
  TCSlib.Cryptography.SecureComputation.encodeCircuit C outs =
      TCSlib.Cryptography.SecureComputation.encodeCircuit C' outs' →
    C = C' ∧ outs = outs'
```

## `TCSlib.Cryptography.SecureComputation.keyAt_yaoSeed`

```lean
TCSlib.Cryptography.SecureComputation.keyAt_yaoSeed : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (r : List Bool) {v : ℕ},
  v < (Y.circ n).size →
    ∀ (b : Bool),
      TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) v b =
        TCSlib.Cryptography.SecureComputation.readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n
```

## `TCSlib.Cryptography.SecureComputation.readBits`

```lean
TCSlib.Cryptography.SecureComputation.readBits : List Bool → ℕ → (len : ℕ) → Fin len → Bool
```

## `TCSlib.Cryptography.SecureComputation.readBits_apply`

```lean
TCSlib.Cryptography.SecureComputation.readBits_apply : ∀ (w : List Bool) (off len : ℕ) (t : Fin len),
  TCSlib.Cryptography.SecureComputation.readBits w off len t = w.getD (off + ↑t) false
```

## `TCSlib.Cryptography.SecureComputation.xorShift`

```lean
TCSlib.Cryptography.SecureComputation.xorShift : {len : ℕ} → (Fin len → Bool) → Equiv.Perm (Fin len → Bool)
```

## `TCSlib.Cryptography.SecureComputation.xorShift._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.xorShift._proof_1 : ∀ {len : ℕ} (l a : Fin len → Bool),
  (fun p => a p ^^ l p ^^ l p) = a
```

## `TCSlib.Cryptography.SecureComputation.xorShift_apply`

```lean
TCSlib.Cryptography.SecureComputation.xorShift_apply : ∀ {len : ℕ} (l a : Fin len → Bool),
  (TCSlib.Cryptography.SecureComputation.xorShift l) a = fun p => a p ^^ l p
```

## `TCSlib.Cryptography.SecureComputation.xorShift_symm_apply`

```lean
TCSlib.Cryptography.SecureComputation.xorShift_symm_apply : ∀ {len : ℕ} (l a : Fin len → Bool),
  (Equiv.symm (TCSlib.Cryptography.SecureComputation.xorShift l)) a = fun p => a p ^^ l p
```

## `TCSlib.Cryptography.SecureComputation.yaoAlice`

```lean
TCSlib.Cryptography.SecureComputation.yaoAlice : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) → (List Bool → List Bool) → TCSlib.Cryptography.Strategy
```

## `TCSlib.Cryptography.SecureComputation.yaoAlice.match_1`

```lean
TCSlib.Cryptography.SecureComputation.yaoAlice.match_1 : (motive : List (List Bool) → Sort u_1) →
  (hist : List (List Bool)) →
    (Unit → motive []) → ((m : List Bool) → (tail : List (List Bool)) → motive (m :: tail)) → motive hist
```

## `TCSlib.Cryptography.SecureComputation.yaoAlice_coins`

```lean
TCSlib.Cryptography.SecureComputation.yaoAlice_coins : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoAlice Y E₁ E₂).coins = TCSlib.Cryptography.SecureComputation.yaoCoins Y
```

## `TCSlib.Cryptography.SecureComputation.yaoAlice_next_cons`

```lean
TCSlib.Cryptography.SecureComputation.yaoAlice_next_cons : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (x z r m : List Bool)
  (hist : List (List Bool)), (TCSlib.Cryptography.SecureComputation.yaoAlice Y E₁ E₂).next x z r (m :: hist) = m
```

## `TCSlib.Cryptography.SecureComputation.yaoAlice_next_nil`

```lean
TCSlib.Cryptography.SecureComputation.yaoAlice_next_nil : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (x z r : List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoAlice Y E₁ E₂).next x z r [] =
    TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ x.length (Complexity.pairFstD z) r
```

## `TCSlib.Cryptography.SecureComputation.yaoBob`

```lean
TCSlib.Cryptography.SecureComputation.yaoBob : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) → (List Bool → List Bool) → TCSlib.Cryptography.Strategy
```

## `TCSlib.Cryptography.SecureComputation.yaoBobInit`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobInit : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (n : ℕ) → List Bool → List Bool → List (Fin n → Bool)
```

## `TCSlib.Cryptography.SecureComputation.yaoBobInit_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobInit_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (msg ans : List Bool),
  TCSlib.Cryptography.SecureComputation.yaoBobInit Y n msg ans =
    List.ofFn fun v =>
      if ↑v < Y.inA.eval n then
        TCSlib.Cryptography.padFin n
          ((TCSlib.Cryptography.SecureComputation.decodeMsgs (Complexity.pairFstD (Complexity.pairSndD msg))).getD ↑v
            [])
      else TCSlib.Cryptography.SecureComputation.readBits ans ((↑v - Y.inA.eval n) * n) n
```

## `TCSlib.Cryptography.SecureComputation.yaoBobInit_yaoMsg`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobInit_yaoMsg : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
  (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool),
  (∀ (i : Fin (Y.inB.eval n)) (t : Fin n),
      ans.getD (↑i * n + ↑t) false =
        TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
          (Y.inA.eval n + ↑i) (y i) t) →
    TCSlib.Cryptography.SecureComputation.yaoBobInit Y n
        (TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      TCSlib.Cryptography.SecureComputation.inputKeys (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
        (Fin.append x y)
```

## `TCSlib.Cryptography.SecureComputation.yaoBobInit_yaoMsg._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobInit_yaoMsg._proof_1_1 : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (v : Fin (Y.inA.eval n + Y.inB.eval n)),
  ¬↑v < Y.inA.eval n → ¬↑v - Y.inA.eval n < Y.inB.eval n → False
```

## `TCSlib.Cryptography.SecureComputation.yaoBobInit_yaoMsg._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobInit_yaoMsg._proof_1_2 : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (v : Fin (Y.inA.eval n + Y.inB.eval n)),
  ¬↑v < Y.inA.eval n → ¬Y.inA.eval n + (↑v - Y.inA.eval n) = ↑v → False
```

## `TCSlib.Cryptography.SecureComputation.yaoBobOut`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobOut : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) → (List Bool → List Bool) → ℕ → List Bool → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.yaoBobOut_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobOut_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (msg ans : List Bool),
  TCSlib.Cryptography.SecureComputation.yaoBobOut Y E₁ E₂ n msg ans =
    List.ofFn fun j =>
      TCSlib.Cryptography.SecureComputation.decodeOut
        (List.ofFn ((TCSlib.Cryptography.SecureComputation.yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
        ((TCSlib.Cryptography.SecureComputation.decodeMsgs (Complexity.pairSndD (Complexity.pairSndD msg))).getD ↑j [])
```

## `TCSlib.Cryptography.SecureComputation.yaoBobOut_yaoMsg`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobOut_yaoMsg : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
  (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool),
  (∀ (i : Fin (Y.inB.eval n)) (t : Fin n),
      ans.getD (↑i * n + ↑t) false =
        TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
          (Y.inA.eval n + ↑i) (y i) t) →
    TCSlib.Cryptography.SecureComputation.Good (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (Y.circ n)
        (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) →
      (∀ (j : Fin (Y.outLen.eval n)),
          TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
              (Y.outs n j) false ≠
            TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
              (Y.outs n j) true) →
        TCSlib.Cryptography.SecureComputation.yaoBobOut Y E₁ E₂ n
            (TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
          List.ofFn (Y.output n x y)
```

## `TCSlib.Cryptography.SecureComputation.yaoBobTables`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobTables : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  ℕ → List Bool → ℕ → List (List Bool)
```

## `TCSlib.Cryptography.SecureComputation.yaoBobTables_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobTables_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (msg : List Bool) (v : ℕ),
  TCSlib.Cryptography.SecureComputation.yaoBobTables Y n msg v =
    if Y.inA.eval n + Y.inB.eval n ≤ v then
      TCSlib.Cryptography.SecureComputation.decodeMsgs
        ((TCSlib.Cryptography.SecureComputation.decodeMsgs (Complexity.pairFstD msg)).getD
          (v - (Y.inA.eval n + Y.inB.eval n)) [])
    else []
```

## `TCSlib.Cryptography.SecureComputation.yaoBobTables_yaoMsg`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobTables_yaoMsg : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ) (xs r : List Bool),
  TCSlib.Cryptography.SecureComputation.yaoBobTables Y n (TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ n xs r) =
    TCSlib.Cryptography.SecureComputation.tableAt (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n)
      (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
```

## `TCSlib.Cryptography.SecureComputation.yaoBobTables_yaoMsg._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobTables_yaoMsg._proof_1_1 : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n v : ℕ),
  ¬v - (Y.inA.eval n + Y.inB.eval n) < (Y.circ n).gates.length →
    ¬(Y.circ n).gates.length ≤ v - (Y.inA.eval n + Y.inB.eval n) → False
```

## `TCSlib.Cryptography.SecureComputation.yaoBobValues`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobValues : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) → (List Bool → List Bool) → (n : ℕ) → List Bool → List Bool → List (Fin n → Bool)
```

## `TCSlib.Cryptography.SecureComputation.yaoBobValues_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobValues_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (msg ans : List Bool),
  TCSlib.Cryptography.SecureComputation.yaoBobValues Y E₁ E₂ n msg ans =
    BoolCircuit.runWith
      (fun g vs =>
        TCSlib.Cryptography.SecureComputation.evalGate (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n)
          (TCSlib.Cryptography.SecureComputation.yaoBobTables Y n msg) vs.length g vs)
      (Y.circ n).gates (TCSlib.Cryptography.SecureComputation.yaoBobInit Y n msg ans)
```

## `TCSlib.Cryptography.SecureComputation.yaoBobValues_yaoMsg`

```lean
TCSlib.Cryptography.SecureComputation.yaoBobValues_yaoMsg : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
  (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool),
  (∀ (i : Fin (Y.inB.eval n)) (t : Fin n),
      ans.getD (↑i * n + ↑t) false =
        TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
          (Y.inA.eval n + ↑i) (y i) t) →
    TCSlib.Cryptography.SecureComputation.yaoBobValues Y E₁ E₂ n
        (TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      TCSlib.Cryptography.SecureComputation.garbledValues (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n)
        (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
        (TCSlib.Cryptography.SecureComputation.inputKeys (Y.circ n)
          (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) (Fin.append x y))
```

## `TCSlib.Cryptography.SecureComputation.yaoBob_coins`

```lean
TCSlib.Cryptography.SecureComputation.yaoBob_coins : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoBob Y E₁ E₂).coins = Complexity.PolyExpr.const 0
```

## `TCSlib.Cryptography.SecureComputation.yaoBob_next`

```lean
TCSlib.Cryptography.SecureComputation.yaoBob_next : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (x z r : List Bool) (hist : List (List Bool)),
  (TCSlib.Cryptography.SecureComputation.yaoBob Y E₁ E₂).next x z r hist =
    TCSlib.Cryptography.SecureComputation.yaoBobOut Y E₁ E₂ x.length (hist.headD []) (Complexity.pairSndD z)
```

## `TCSlib.Cryptography.SecureComputation.yaoCall`

```lean
TCSlib.Cryptography.SecureComputation.yaoCall : (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) →
  (n : ℕ) → Fin (Y.inB.eval n * n) → Fin (Y.inB.eval n) × Fin n
```

## `TCSlib.Cryptography.SecureComputation.yaoCall.eq_1`

```lean
TCSlib.Cryptography.SecureComputation.yaoCall.eq_1 : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (j : Fin (Y.inB.eval n * n)), TCSlib.Cryptography.SecureComputation.yaoCall Y n j = finProdFinEquiv.symm j
```

## `TCSlib.Cryptography.SecureComputation.yaoCall_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoCall_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (j : Fin (Y.inB.eval n * n)), TCSlib.Cryptography.SecureComputation.yaoCall Y n j = finProdFinEquiv.symm j
```

## `TCSlib.Cryptography.SecureComputation.yaoCall_finProdFinEquiv`

```lean
TCSlib.Cryptography.SecureComputation.yaoCall_finProdFinEquiv : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (i : Fin (Y.inB.eval n)) (t : Fin n),
  TCSlib.Cryptography.SecureComputation.yaoCall Y n (finProdFinEquiv (i, t)) = (i, t)
```

## `TCSlib.Cryptography.SecureComputation.yaoCoins`

```lean
TCSlib.Cryptography.SecureComputation.yaoCoins : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  Complexity.PolyExpr
```

## `TCSlib.Cryptography.SecureComputation.yaoCoins_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoCoins_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit),
  TCSlib.Cryptography.SecureComputation.yaoCoins Y =
    (((Complexity.PolyExpr.const 10).mul Y.sizeBound).mul Complexity.PolyExpr.var).add
      ((Complexity.PolyExpr.const 2).mul Y.sizeBound)
```

## `TCSlib.Cryptography.SecureComputation.yaoCoins_eval`

```lean
TCSlib.Cryptography.SecureComputation.yaoCoins_eval : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ),
  (TCSlib.Cryptography.SecureComputation.yaoCoins Y).eval n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n
```

## `TCSlib.Cryptography.SecureComputation.yaoFunctionality`

```lean
TCSlib.Cryptography.SecureComputation.yaoFunctionality : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  TCSlib.Cryptography.SecureComputation.Functionality
```

## `TCSlib.Cryptography.SecureComputation.yaoFunctionality_f`

```lean
TCSlib.Cryptography.SecureComputation.yaoFunctionality_f : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
  (y : Fin (Y.inB.eval n) → Bool),
  (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).f n x y = (Y.output n x y, Y.output n x y)
```

## `TCSlib.Cryptography.SecureComputation.yaoFunctionality_inA`

```lean
TCSlib.Cryptography.SecureComputation.yaoFunctionality_inA : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit),
  (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).inA = Y.inA
```

## `TCSlib.Cryptography.SecureComputation.yaoFunctionality_inB`

```lean
TCSlib.Cryptography.SecureComputation.yaoFunctionality_inB : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit),
  (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).inB = Y.inB
```

## `TCSlib.Cryptography.SecureComputation.yaoFunctionality_outA`

```lean
TCSlib.Cryptography.SecureComputation.yaoFunctionality_outA : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit),
  (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).outA = Y.outLen
```

## `TCSlib.Cryptography.SecureComputation.yaoFunctionality_outB`

```lean
TCSlib.Cryptography.SecureComputation.yaoFunctionality_outB : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit),
  (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).outB = Y.outLen
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) →
    (List Bool → List Bool) →
      TCSlib.Cryptography.SecureComputation.HybridProtocol TCSlib.Cryptography.SecureComputation.otFunctionality
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_answersB_getD`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_answersB_getD : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
  (xs ys rA rB : List Bool) (i : Fin (Y.inB.eval n)) (t : Fin n),
  ((TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).answersB n xs ys rA rB).getD (↑i * n + ↑t) false =
    TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n rA)
      (Y.inA.eval n + ↑i) (ys.getD (↑i) false) t
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_callA`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_callA : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (xs r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 2),
  (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).callA n xs r j (Fin.cast ⋯ c) =
    TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
      (Y.inA.eval n + ↑(TCSlib.Cryptography.SecureComputation.yaoCall Y n j).1) (decide (↑c = 1))
      (TCSlib.Cryptography.SecureComputation.yaoCall Y n j).2
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_callB`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_callB : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (ys r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 1),
  (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).callB n ys r j (Fin.cast ⋯ c) =
    ys.getD (↑(TCSlib.Cryptography.SecureComputation.yaoCall Y n j).1) false
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_calls`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_calls : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).calls = Y.inB.mul Complexity.PolyExpr.var
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_correct`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_correct : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
  (x : Fin ((TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).inA.eval n) → Bool)
  (y : Fin ((TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).inB.eval n) → Bool)
  (r : (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).Coins n),
  TCSlib.Cryptography.SecureComputation.Good (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (Y.circ n)
      (TCSlib.Cryptography.SecureComputation.yaoSeed Y n (List.ofFn r.1)) →
    (∀ (j : Fin (Y.outLen.eval n)),
        TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n)
            (TCSlib.Cryptography.SecureComputation.yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) false ≠
          TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n)
            (TCSlib.Cryptography.SecureComputation.yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) true) →
      (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).main.outV
            (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).main.P (List.replicate n true)
            ((TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y)
              (List.ofFn r.1) (List.ofFn r.2))
            ((TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y)
              (List.ofFn r.1) (List.ofFn r.2))
            r =
          List.ofFn ((TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).f n x y).2 ∧
        (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).main.outP (List.replicate n true)
            ((TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y)
              (List.ofFn r.1) (List.ofFn r.2))
            ((TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y)
              (List.ofFn r.1) (List.ofFn r.2))
            r =
          List.ofFn ((TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).f n x y).1
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_hbcSecure`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_hbcSecure : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ :
    (n : ℕ) →
      (Fin n → Bool) →
        (Fin n → Bool) →
          Fin ((Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen).eval n) → Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
      Complexity.PolyTimeComputable E₁ →
        Complexity.PolyTimeComputable E₂ →
          TCSlib.Cryptography.SecureComputation.PRFOut (Complexity.PolyExpr.var.add Complexity.PolyExpr.var) G₁ →
            TCSlib.Cryptography.SecureComputation.PRFOut
                (Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen) G₂ →
              (TCSlib.Cryptography.SecureComputation.PRFOut
                  ((Complexity.PolyExpr.var.add Complexity.PolyExpr.var).add
                    (Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen))
                  fun n s x => Fin.append (G₁ n s x) (G₂ n s x)) →
                (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).HBCSecure
                  (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y)
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_main`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_main : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).main = TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool),
  Complexity.PolyTimeComputable E₁ →
    Complexity.PolyTimeComputable E₂ →
      (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).PolyTime
        (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y)
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime._proof_1_1`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime._proof_1_1 : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (i : Fin (Y.inB.eval n)) (t : Fin n),
  ¬Y.inA.eval n + ↑(i, t).1 < Y.inA.eval n + Y.inB.eval n + (Y.circ n).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime._proof_1_2 : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) (w r : List Bool),
  Y.inA.eval w.length + Y.inB.eval w.length + (Y.circ w.length).gates.length ≤ Y.sizeBound.eval w.length →
    ¬(Y.circ w.length).gates.length ≤ Y.sizeBound.eval w.length → False
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ :
    (n : ℕ) →
      (Fin n → Bool) →
        (Fin n → Bool) →
          Fin ((Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen).eval n) → Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
      Complexity.PolyTimeComputable E₁ →
        Complexity.PolyTimeComputable E₂ →
          TCSlib.Cryptography.SecureComputation.PRFOut (Complexity.PolyExpr.var.add Complexity.PolyExpr.var) G₁ →
            TCSlib.Cryptography.SecureComputation.PRFOut
                (Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen) G₂ →
              (TCSlib.Cryptography.SecureComputation.PRFOut
                  ((Complexity.PolyExpr.var.add Complexity.PolyExpr.var).add
                    (Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen))
                  fun n s x => Fin.append (G₁ n s x) (G₂ n s x)) →
                ∃ SA SB,
                  ∀ (D : Complexity.NUPPT),
                    ∃ ε,
                      TCSlib.Cryptography.Negligible ε ∧
                        ∀ (n : ℕ)
                          (x : Fin ((TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).inA.eval n) → Bool)
                          (y : Fin ((TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).inB.eval n) → Bool),
                          TCSlib.Cryptography.distAdv
                                ((TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).realA
                                  (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y) n x y)
                                ((TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).idealA SA n x y)
                                (D.distinguisherL n) ≤
                              ε n ∧
                            TCSlib.Cryptography.distAdv
                                ((TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).realB
                                  (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y) n x y)
                                ((TCSlib.Cryptography.SecureComputation.yaoFunctionality Y).idealB SB n x y)
                                (D.distinguisherL n) ≤
                              ε n
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators._proof_1_2`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators._proof_1_2 : ∀ (n : ℕ),
  ¬7 * n + 2 ≤ n + n + (n + (4 * n + 2)) → False
```

## `TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators._simp_1_1`

```lean
TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators._simp_1_1 : ∀ {α : Type u_1} [inst : Preorder α]
  (a : α), (a ≤ a) = True
```

## `TCSlib.Cryptography.SecureComputation.yaoKeysA`

```lean
TCSlib.Cryptography.SecureComputation.yaoKeysA : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  ℕ → List Bool → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.yaoKeysA_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoKeysA_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (xs r : List Bool),
  TCSlib.Cryptography.SecureComputation.yaoKeysA Y n xs r =
    TCSlib.Cryptography.Strategy.encodeMsgs
      (List.ofFn fun v =>
        List.ofFn
          (TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
            (↑v) (xs.getD (↑v) false)))
```

## `TCSlib.Cryptography.SecureComputation.yaoMain`

```lean
TCSlib.Cryptography.SecureComputation.yaoMain : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) → (List Bool → List Bool) → TCSlib.Cryptography.Protocol
```

## `TCSlib.Cryptography.SecureComputation.yaoMain_P`

```lean
TCSlib.Cryptography.SecureComputation.yaoMain_P : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).P = TCSlib.Cryptography.SecureComputation.yaoAlice Y E₁ E₂
```

## `TCSlib.Cryptography.SecureComputation.yaoMain_V`

```lean
TCSlib.Cryptography.SecureComputation.yaoMain_V : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).V = TCSlib.Cryptography.SecureComputation.yaoBob Y E₁ E₂
```

## `TCSlib.Cryptography.SecureComputation.yaoMain_outP`

```lean
TCSlib.Cryptography.SecureComputation.yaoMain_outP : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (w zA zB : List Bool)
  (r :
    (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).ExecCoins
      (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).P w),
  (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).outP w zA zB r =
    TCSlib.Cryptography.SecureComputation.yaoBobOut Y E₁ E₂ w.length
      (TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ w.length (Complexity.pairFstD zA) (List.ofFn r.1))
      (Complexity.pairSndD zB)
```

## `TCSlib.Cryptography.SecureComputation.yaoMain_outV`

```lean
TCSlib.Cryptography.SecureComputation.yaoMain_outV : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (w zA zB : List Bool)
  (r :
    (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).ExecCoins
      (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).P w),
  (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).outV (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).P
      w zA zB r =
    TCSlib.Cryptography.SecureComputation.yaoBobOut Y E₁ E₂ w.length
      (TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ w.length (Complexity.pairFstD zA) (List.ofFn r.1))
      (Complexity.pairSndD zB)
```

## `TCSlib.Cryptography.SecureComputation.yaoMain_rounds`

```lean
TCSlib.Cryptography.SecureComputation.yaoMain_rounds : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).rounds = Complexity.PolyExpr.const 2
```

## `TCSlib.Cryptography.SecureComputation.yaoMain_verifierFirst`

```lean
TCSlib.Cryptography.SecureComputation.yaoMain_verifierFirst : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoMain Y E₁ E₂).verifierFirst = false
```

## `TCSlib.Cryptography.SecureComputation.yaoMsg`

```lean
TCSlib.Cryptography.SecureComputation.yaoMsg : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) → (List Bool → List Bool) → ℕ → List Bool → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.yaoMsg_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoMsg_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (xs r : List Bool),
  TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ n xs r =
    Turing.pairEncode (TCSlib.Cryptography.SecureComputation.yaoTables Y E₁ E₂ n r)
      (Turing.pairEncode (TCSlib.Cryptography.SecureComputation.yaoKeysA Y n xs r)
        (TCSlib.Cryptography.SecureComputation.yaoPairs Y n r))
```

## `TCSlib.Cryptography.SecureComputation.yaoPairs`

```lean
TCSlib.Cryptography.SecureComputation.yaoPairs : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  ℕ → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.yaoPairs_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoPairs_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.yaoPairs Y n r =
    TCSlib.Cryptography.Strategy.encodeMsgs
      (List.ofFn fun j =>
        Turing.pairEncode
          (List.ofFn
            (TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n)
              (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) (Y.outs n j) false))
          (List.ofFn
            (TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n)
              (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) (Y.outs n j) true)))
```

## `TCSlib.Cryptography.SecureComputation.yaoProtocol`

```lean
TCSlib.Cryptography.SecureComputation.yaoProtocol : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) →
    (List Bool → List Bool) →
      TCSlib.Cryptography.TrapdoorCollection → (List Bool → List Bool) → TCSlib.Cryptography.Protocol
```

## `TCSlib.Cryptography.SecureComputation.yaoProtocol_P`

```lean
TCSlib.Cryptography.SecureComputation.yaoProtocol_P : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (T : TCSlib.Cryptography.TrapdoorCollection) (H : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoProtocol Y E₁ E₂ T H).P =
    (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).composeP
      (TCSlib.Cryptography.SecureComputation.otProtocol T H)
```

## `TCSlib.Cryptography.SecureComputation.yaoProtocol_V`

```lean
TCSlib.Cryptography.SecureComputation.yaoProtocol_V : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (T : TCSlib.Cryptography.TrapdoorCollection) (H : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoProtocol Y E₁ E₂ T H).V =
    (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).composeV
      (TCSlib.Cryptography.SecureComputation.otProtocol T H)
```

## `TCSlib.Cryptography.SecureComputation.yaoProtocol_hbcSecure`

```lean
TCSlib.Cryptography.SecureComputation.yaoProtocol_hbcSecure : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool)
  (T : TCSlib.Cryptography.TrapdoorCollection) (H : List Bool → List Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ :
    (n : ℕ) →
      (Fin n → Bool) →
        (Fin n → Bool) →
          Fin ((Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen).eval n) → Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
      Complexity.PolyTimeComputable E₁ →
        Complexity.PolyTimeComputable E₂ →
          TCSlib.Cryptography.SecureComputation.PRFOut (Complexity.PolyExpr.var.add Complexity.PolyExpr.var) G₁ →
            TCSlib.Cryptography.SecureComputation.PRFOut
                (Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen) G₂ →
              (TCSlib.Cryptography.SecureComputation.PRFOut
                  ((Complexity.PolyExpr.var.add Complexity.PolyExpr.var).add
                    (Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen))
                  fun n s x => Fin.append (G₁ n s x) (G₂ n s x)) →
                ∀ {h : (i : List Bool) → T.D i → Bool},
                  Complexity.PolyTimeComputable H →
                    (∀ (i : List Bool) (x : T.D i), H (Turing.pairEncode i (T.encD i x)) = [h i x]) →
                      T.OneWay →
                        TCSlib.Cryptography.SecureComputation.EnhancedHardCore T h →
                          TCSlib.Cryptography.SecureComputation.HBCSecure
                            (TCSlib.Cryptography.SecureComputation.yaoProtocol Y E₁ E₂ T H)
                            (TCSlib.Cryptography.SecureComputation.yaoFunctionality Y)
```

## `TCSlib.Cryptography.SecureComputation.yaoProtocol_rounds`

```lean
TCSlib.Cryptography.SecureComputation.yaoProtocol_rounds : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool)
  (T : TCSlib.Cryptography.TrapdoorCollection) (H : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoProtocol Y E₁ E₂ T H).rounds =
    (((TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).calls.mul
              ((Complexity.PolyExpr.const 2).mul (TCSlib.Cryptography.SecureComputation.otProtocol T H).rounds)).add
          (Complexity.PolyExpr.const (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).lead)).add
      (TCSlib.Cryptography.SecureComputation.yaoHybrid Y E₁ E₂).main.rounds
```

## `TCSlib.Cryptography.SecureComputation.yaoProtocol_verifierFirst`

```lean
TCSlib.Cryptography.SecureComputation.yaoProtocol_verifierFirst : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool)
  (T : TCSlib.Cryptography.TrapdoorCollection) (H : List Bool → List Bool),
  (TCSlib.Cryptography.SecureComputation.yaoProtocol Y E₁ E₂ T H).verifierFirst = false
```

## `TCSlib.Cryptography.SecureComputation.yaoSeed`

```lean
TCSlib.Cryptography.SecureComputation.yaoSeed : (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) →
  (n : ℕ) →
    List Bool →
      TCSlib.Cryptography.SecureComputation.GarbleSeed (Y.circ n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))
```

## `TCSlib.Cryptography.SecureComputation.yaoSeed._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.yaoSeed._proof_1 : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ) (i : Fin (Y.circ n).gates.length),
  ↑i < (Y.circ n).gates.length
```

## `TCSlib.Cryptography.SecureComputation.yaoSeed_fst`

```lean
TCSlib.Cryptography.SecureComputation.yaoSeed_fst : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (r : List Bool) (v : Fin (Y.circ n).size) (b : Bool),
  (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r).1 v b =
    TCSlib.Cryptography.SecureComputation.readBits r ((b.toNat * Y.sizeBound.eval n + ↑v) * n) n
```

## `TCSlib.Cryptography.SecureComputation.yaoSeed_good_whp`

```lean
TCSlib.Cryptography.SecureComputation.yaoSeed_good_whp : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool)
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ :
    (n : ℕ) →
      (Fin n → Bool) →
        (Fin n → Bool) →
          Fin ((Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen).eval n) → Bool),
  (∀ (n : ℕ) (s x : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₁ n s x)) →
    (∀ (n : ℕ) (s x : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G₂ n s x)) →
      TCSlib.Cryptography.SecureComputation.PRFOut (Complexity.PolyExpr.var.add Complexity.PolyExpr.var) G₁ →
        TCSlib.Cryptography.SecureComputation.PRFOut
            (Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen) G₂ →
          ∃ δ,
            TCSlib.Cryptography.Negligible δ ∧
              ∀ (n : ℕ),
                (TCSlib.Cryptography.uprob fun r =>
                    ¬(TCSlib.Cryptography.SecureComputation.Good
                          (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (Y.circ n)
                          (TCSlib.Cryptography.SecureComputation.yaoSeed Y n (List.ofFn r)) ∧
                        ∀ (j : Fin (Y.outLen.eval n)),
                          TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n)
                              (TCSlib.Cryptography.SecureComputation.yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
                            TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n)
                              (TCSlib.Cryptography.SecureComputation.yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤
                  δ n
```

## `TCSlib.Cryptography.SecureComputation.yaoSeed_snd_fst`

```lean
TCSlib.Cryptography.SecureComputation.yaoSeed_snd_fst : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (r : List Bool) (i : Fin (Y.circ n).gates.length) (a : Fin (Y.circ n).gates[i].args.length → Bool),
  (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r).2.1 i a =
    (TCSlib.Cryptography.SecureComputation.readBits r
        (2 * Y.sizeBound.eval n * n + (4 * ↑i + TCSlib.Cryptography.SecureComputation.assignIdx a) * (2 * n)) n,
      TCSlib.Cryptography.SecureComputation.readBits r
        (2 * Y.sizeBound.eval n * n + (4 * ↑i + TCSlib.Cryptography.SecureComputation.assignIdx a) * (2 * n) + n) n)
```

## `TCSlib.Cryptography.SecureComputation.yaoSeed_snd_fst._proof_1`

```lean
TCSlib.Cryptography.SecureComputation.yaoSeed_snd_fst._proof_1 : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (n : ℕ),
  ¬(Y.circ n).gates.length ≤ (Y.circ n).gates.length → False
```

## `TCSlib.Cryptography.SecureComputation.yaoSeed_snd_snd`

```lean
TCSlib.Cryptography.SecureComputation.yaoSeed_snd_snd : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (n : ℕ) (r : List Bool) (i : Fin (Y.circ n).gates.length),
  (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r).2.2 i =
    TCSlib.Cryptography.SecureComputation.xorShift
      (TCSlib.Cryptography.SecureComputation.readBits r (10 * Y.sizeBound.eval n * n + 2 * ↑i)
        (Y.circ n).gates[i].args.length)
```

## `TCSlib.Cryptography.SecureComputation.yaoTables`

```lean
TCSlib.Cryptography.SecureComputation.yaoTables : TCSlib.Cryptography.SecureComputation.YaoCircuit →
  (List Bool → List Bool) → (List Bool → List Bool) → ℕ → List Bool → List Bool
```

## `TCSlib.Cryptography.SecureComputation.yaoTables_eq`

```lean
TCSlib.Cryptography.SecureComputation.yaoTables_eq : ∀ (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit)
  (E₁ E₂ : List Bool → List Bool) (n : ℕ) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.yaoTables Y E₁ E₂ n r =
    TCSlib.Cryptography.Strategy.encodeMsgs
      (List.ofFn fun i =>
        TCSlib.Cryptography.Strategy.encodeMsgs
          (TCSlib.Cryptography.SecureComputation.garbledTable
            (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n) (Y.circ n)
            (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) i))
```

## `_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.eq_1`

```lean
_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.eq_1 : ∀
  (motive : BoolCircuit.GateKind → Sort u_1) (h_1 : Unit → motive BoolCircuit.GateKind.and)
  (h_2 : Unit → motive BoolCircuit.GateKind.or) (h_3 : Unit → motive BoolCircuit.GateKind.not),
  (match BoolCircuit.GateKind.and with
    | BoolCircuit.GateKind.and => h_1 ()
    | BoolCircuit.GateKind.or => h_2 ()
    | BoolCircuit.GateKind.not => h_3 ()) =
    h_1 ()
```

## `_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.eq_2`

```lean
_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.eq_2 : ∀
  (motive : BoolCircuit.GateKind → Sort u_1) (h_1 : Unit → motive BoolCircuit.GateKind.and)
  (h_2 : Unit → motive BoolCircuit.GateKind.or) (h_3 : Unit → motive BoolCircuit.GateKind.not),
  (match BoolCircuit.GateKind.or with
    | BoolCircuit.GateKind.and => h_1 ()
    | BoolCircuit.GateKind.or => h_2 ()
    | BoolCircuit.GateKind.not => h_3 ()) =
    h_2 ()
```

## `_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.eq_3`

```lean
_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.eq_3 : ∀
  (motive : BoolCircuit.GateKind → Sort u_1) (h_1 : Unit → motive BoolCircuit.GateKind.and)
  (h_2 : Unit → motive BoolCircuit.GateKind.or) (h_3 : Unit → motive BoolCircuit.GateKind.not),
  (match BoolCircuit.GateKind.not with
    | BoolCircuit.GateKind.and => h_1 ()
    | BoolCircuit.GateKind.or => h_2 ()
    | BoolCircuit.GateKind.not => h_3 ()) =
    h_3 ()
```

## `_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.splitter`

```lean
_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.splitter : (motive :
    BoolCircuit.GateKind → Sort u_1) →
  (x : BoolCircuit.GateKind) →
    motive BoolCircuit.GateKind.and → motive BoolCircuit.GateKind.or → motive BoolCircuit.GateKind.not → motive x
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.DAGGate.encode_prefixFree`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.DAGGate.encode_prefixFree : BoolCircuit.PrefixFree✝
  BoolCircuit.DAGGate.encode
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode.match_1.eq_1`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode.match_1.eq_1 : ∀
  (motive : BoolCircuit.GateKind → Sort u_1) (h_1 : Unit → motive BoolCircuit.GateKind.and)
  (h_2 : Unit → motive BoolCircuit.GateKind.or) (h_3 : Unit → motive BoolCircuit.GateKind.not),
  (match BoolCircuit.GateKind.and with
    | BoolCircuit.GateKind.and => h_1 ()
    | BoolCircuit.GateKind.or => h_2 ()
    | BoolCircuit.GateKind.not => h_3 ()) =
    h_1 ()
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode.match_1.eq_2`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode.match_1.eq_2 : ∀
  (motive : BoolCircuit.GateKind → Sort u_1) (h_1 : Unit → motive BoolCircuit.GateKind.and)
  (h_2 : Unit → motive BoolCircuit.GateKind.or) (h_3 : Unit → motive BoolCircuit.GateKind.not),
  (match BoolCircuit.GateKind.or with
    | BoolCircuit.GateKind.and => h_1 ()
    | BoolCircuit.GateKind.or => h_2 ()
    | BoolCircuit.GateKind.not => h_3 ()) =
    h_2 ()
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode.match_1.eq_3`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode.match_1.eq_3 : ∀
  (motive : BoolCircuit.GateKind → Sort u_1) (h_1 : Unit → motive BoolCircuit.GateKind.and)
  (h_2 : Unit → motive BoolCircuit.GateKind.or) (h_3 : Unit → motive BoolCircuit.GateKind.not),
  (match BoolCircuit.GateKind.not with
    | BoolCircuit.GateKind.and => h_1 ()
    | BoolCircuit.GateKind.or => h_2 ()
    | BoolCircuit.GateKind.not => h_3 ()) =
    h_3 ()
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode.match_1.splitter`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode.match_1.splitter : (motive :
    BoolCircuit.GateKind → Sort u_1) →
  (x : BoolCircuit.GateKind) →
    motive BoolCircuit.GateKind.and → motive BoolCircuit.GateKind.or → motive BoolCircuit.GateKind.not → motive x
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode_prefixFree`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.GateKind.encode_prefixFree : BoolCircuit.PrefixFree✝
  BoolCircuit.GateKind.encode
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.PrefixFree`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.PrefixFree : {α : Type} →
  (α → List Bool) → Prop
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeList.match_1.eq_1`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeList.match_1.eq_1 : ∀ {α : Type}
  (motive : List α → Sort u_1) (h_1 : Unit → motive []) (h_2 : (a : α) → (as : List α) → motive (a :: as)),
  (match [] with
    | [] => h_1 ()
    | a :: as => h_2 a as) =
    h_1 ()
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeList.match_1.eq_2`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeList.match_1.eq_2 : ∀ {α : Type}
  (motive : List α → Sort u_1) (a : α) (as : List α) (h_1 : Unit → motive [])
  (h_2 : (a : α) → (as : List α) → motive (a :: as)),
  (match a :: as with
    | [] => h_1 ()
    | a :: as => h_2 a as) =
    h_2 a as
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeList.match_1.splitter`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeList.match_1.splitter : {α : Type} →
  (motive : List α → Sort u_1) → (x : List α) → motive [] → ((a : α) → (as : List α) → motive (a :: as)) → motive x
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeList_prefixFree`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeList_prefixFree : ∀ {α : Type}
  {f : α → List Bool}, BoolCircuit.PrefixFree✝ f → BoolCircuit.PrefixFree✝¹ (BoolCircuit.encodeList f)
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeNat_prefixFree`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.encodeNat_prefixFree : BoolCircuit.PrefixFree✝
  BoolCircuit.encodeNat
```

## `_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.length_encodeList_le`

```lean
_private.TCSlib.Complexity.CircuitComplexity.Uniform.0.BoolCircuit.length_encodeList_le : ∀ {α : Type}
  (f : α → List Bool) (B : ℕ) (as : List α),
  (∀ a ∈ as, (f a).length ≤ B) → (BoolCircuit.encodeList f as).length ≤ as.length * (B + 1) + 1
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.encodeMsgs_inj`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.encodeMsgs_inj : ∀
  {l l' : List (List Bool)},
  l.length = l'.length → TCSlib.Cryptography.Strategy.encodeMsgs l = TCSlib.Cryptography.Strategy.encodeMsgs l' → l = l'
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.encodeMsgs_inj.match_1_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.encodeMsgs_inj.match_1_1 : ∀
  (motive :
    (x x_1 : List (List Bool)) →
      x.length = x_1.length →
        TCSlib.Cryptography.Strategy.encodeMsgs x = TCSlib.Cryptography.Strategy.encodeMsgs x_1 → Prop)
  (x x_1 : List (List Bool)) (x_2 : x.length = x_1.length)
  (x_3 : TCSlib.Cryptography.Strategy.encodeMsgs x = TCSlib.Cryptography.Strategy.encodeMsgs x_1),
  (∀ (x : [].length = [].length)
      (x_4 : TCSlib.Cryptography.Strategy.encodeMsgs [] = TCSlib.Cryptography.Strategy.encodeMsgs []),
      motive [] [] x x_4) →
    (∀ (a : List Bool) (l : List (List Bool)) (b : List Bool) (l' : List (List Bool))
        (hlen : (a :: l).length = (b :: l').length)
        (h : TCSlib.Cryptography.Strategy.encodeMsgs (a :: l) = TCSlib.Cryptography.Strategy.encodeMsgs (b :: l')),
        motive (a :: l) (b :: l') hlen h) →
      motive x x_1 x_2 x_3
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.encodeNat_inj`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.encodeNat_inj : ∀
  {a b : ℕ}, BoolCircuit.encodeNat a = BoolCircuit.encodeNat b → a = b
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.getD_ofFn'`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.getD_ofFn' : ∀
  {α : Type} {k : ℕ} (f : Fin k → α) (i : Fin k) (d : α), (List.ofFn f).getD (↑i) d = f i
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.yaoBobOut_yaoMsg_of_eq`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.0.TCSlib.Cryptography.SecureComputation.yaoBobOut_yaoMsg_of_eq : ∀
  (Y : TCSlib.Cryptography.SecureComputation.YaoCircuit) (E₁ E₂ : List Bool → List Bool) {L n : ℕ},
  L = n →
    ∀ (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool),
      (∀ (i : Fin (Y.inB.eval n)) (t : Fin n),
          ans.getD (↑i * n + ↑t) false =
            TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r)
              (Y.inA.eval n + ↑i) (y i) t) →
        TCSlib.Cryptography.SecureComputation.Good (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n)
            (Y.circ n) (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) →
          (∀ (j : Fin (Y.outLen.eval n)),
              TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n)
                  (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) (Y.outs n j) false ≠
                TCSlib.Cryptography.SecureComputation.keyAt (Y.circ n)
                  (TCSlib.Cryptography.SecureComputation.yaoSeed Y n r) (Y.outs n j) true) →
            TCSlib.Cryptography.SecureComputation.yaoBobOut Y E₁ E₂ L
                (TCSlib.Cryptography.SecureComputation.yaoMsg Y E₁ E₂ L (List.ofFn x) r) ans =
              List.ofFn (Y.output n x y)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStageZero.0._proof_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStageZero.0._proof_7 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStageZero.0._proof_8`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStageZero.0._proof_8 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (S : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.ChunkScanner.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.table4_poly`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.ChunkScanner.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.table4_poly : ∀
  (F : Bool → Bool → Bool → Bool → List Bool) {a b c d : List Bool → Bool},
  (Complexity.PolyTimeComputable fun w => [a w]) →
    (Complexity.PolyTimeComputable fun w => [b w]) →
      (Complexity.PolyTimeComputable fun w => [c w]) →
        (Complexity.PolyTimeComputable fun w => [d w]) →
          Complexity.PolyTimeComputable fun w => F (a w) (b w) (c w) (d w)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option.match_1.eq_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option.match_1.eq_1 : ∀
  (N : List Bool) (motive : Option (Fin N.length → Bool) → Sort u_1) (h_1 : Unit → motive none)
  (h_2 : (k : Fin N.length → Bool) → motive (some k)),
  (match none with
    | none => h_1 ()
    | some k => h_2 k) =
    h_1 ()
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option.match_1.eq_2`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option.match_1.eq_2 : ∀
  (N : List Bool) (motive : Option (Fin N.length → Bool) → Sort u_1) (k : Fin N.length → Bool)
  (h_1 : Unit → motive none) (h_2 : (k : Fin N.length → Bool) → motive (some k)),
  (match some k with
    | none => h_1 ()
    | some k => h_2 k) =
    h_2 k
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option.match_1.splitter`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.checkFinTagged_option.match_1.splitter : (N :
    List Bool) →
  (motive : Option (Fin N.length → Bool) → Sort u_1) →
    (x : Option (Fin N.length → Bool)) → motive none → ((k : Fin N.length → Bool) → motive (some k)) → motive x
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged.match_1.eq_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged.match_1.eq_1 : ∀
  (motive : Option (List Bool) → Sort u_1) (h_1 : Unit → motive none) (h_2 : (m : List Bool) → motive (some m)),
  (match none with
    | none => h_1 ()
    | some m => h_2 m) =
    h_1 ()
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged.match_1.eq_2`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged.match_1.eq_2 : ∀
  (motive : Option (List Bool) → Sort u_1) (m : List Bool) (h_1 : Unit → motive none)
  (h_2 : (m : List Bool) → motive (some m)),
  (match some m with
    | none => h_1 ()
    | some m => h_2 m) =
    h_2 m
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged.match_1.splitter`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.specialDecTagged.match_1.splitter : (motive :
    Option (List Bool) → Sort u_1) →
  (x : Option (List Bool)) → motive none → ((m : List Bool) → motive (some m)) → motive x
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.dbl_pair`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.dbl_pair : ∀
  (a b : List Bool),
  Turing.dbl (Turing.pairEncode a b) = Turing.dbl (Turing.dbl a) ++ [false, false, true, true] ++ Turing.dbl b
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
  Bool → TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_1 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝ (false, false, false) x =
    if x = true then (false, false, false) else (false, false, true)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_2`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_2 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝ (false, false, true) x =
    if x = true then (false, true, false) else (true, true, false)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_3`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_3 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝ (false, true, false) x =
    (false, true, true)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_4`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_4 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝ (false, true, true) x =
    (true, false, false)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_5`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_5 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝ (true, false, false) x =
    if x = true then (true, false, true) else (false, false, true)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_6`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_6 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝ (true, false, true) x =
    if x = true then (true, false, true) else (true, false, false)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.eq_7 : ∀
  (x c : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝ (true, true, c) x = (true, true, c)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1 : (motive :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) →
  (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) →
    (x_1 : Bool) →
      ((b : Bool) → motive (false, false, false) b) →
        ((b : Bool) → motive (false, false, true) b) →
          ((x : Bool) → motive (false, true, false) x) →
            ((x : Bool) → motive (false, true, true) x) →
              ((b : Bool) → motive (true, false, false) b) →
                ((b : Bool) → motive (true, false, true) b) → ((c x : Bool) → motive (true, true, c) x) → motive x x_1
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_1 : ∀
  (motive : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) (b : Bool)
  (h_1 : (b : Bool) → motive (false, false, false) b) (h_2 : (b : Bool) → motive (false, false, true) b)
  (h_3 : (x : Bool) → motive (false, true, false) x) (h_4 : (x : Bool) → motive (false, true, true) x)
  (h_5 : (b : Bool) → motive (true, false, false) b) (h_6 : (b : Bool) → motive (true, false, true) b)
  (h_7 : (c x : Bool) → motive (true, true, c) x),
  (match (false, false, false), b with
    | (false, false, false), b => h_1 b
    | (false, false, true), b => h_2 b
    | (false, true, false), x => h_3 x
    | (false, true, true), x => h_4 x
    | (true, false, false), b => h_5 b
    | (true, false, true), b => h_6 b
    | (true, true, c), x => h_7 c x) =
    h_1 b
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_2`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_2 : ∀
  (motive : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) (b : Bool)
  (h_1 : (b : Bool) → motive (false, false, false) b) (h_2 : (b : Bool) → motive (false, false, true) b)
  (h_3 : (x : Bool) → motive (false, true, false) x) (h_4 : (x : Bool) → motive (false, true, true) x)
  (h_5 : (b : Bool) → motive (true, false, false) b) (h_6 : (b : Bool) → motive (true, false, true) b)
  (h_7 : (c x : Bool) → motive (true, true, c) x),
  (match (false, false, true), b with
    | (false, false, false), b => h_1 b
    | (false, false, true), b => h_2 b
    | (false, true, false), x => h_3 x
    | (false, true, true), x => h_4 x
    | (true, false, false), b => h_5 b
    | (true, false, true), b => h_6 b
    | (true, true, c), x => h_7 c x) =
    h_2 b
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_3`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_3 : ∀
  (motive : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) (x : Bool)
  (h_1 : (b : Bool) → motive (false, false, false) b) (h_2 : (b : Bool) → motive (false, false, true) b)
  (h_3 : (x : Bool) → motive (false, true, false) x) (h_4 : (x : Bool) → motive (false, true, true) x)
  (h_5 : (b : Bool) → motive (true, false, false) b) (h_6 : (b : Bool) → motive (true, false, true) b)
  (h_7 : (c x : Bool) → motive (true, true, c) x),
  (match (false, true, false), x with
    | (false, false, false), b => h_1 b
    | (false, false, true), b => h_2 b
    | (false, true, false), x => h_3 x
    | (false, true, true), x => h_4 x
    | (true, false, false), b => h_5 b
    | (true, false, true), b => h_6 b
    | (true, true, c), x => h_7 c x) =
    h_3 x
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_4`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_4 : ∀
  (motive : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) (x : Bool)
  (h_1 : (b : Bool) → motive (false, false, false) b) (h_2 : (b : Bool) → motive (false, false, true) b)
  (h_3 : (x : Bool) → motive (false, true, false) x) (h_4 : (x : Bool) → motive (false, true, true) x)
  (h_5 : (b : Bool) → motive (true, false, false) b) (h_6 : (b : Bool) → motive (true, false, true) b)
  (h_7 : (c x : Bool) → motive (true, true, c) x),
  (match (false, true, true), x with
    | (false, false, false), b => h_1 b
    | (false, false, true), b => h_2 b
    | (false, true, false), x => h_3 x
    | (false, true, true), x => h_4 x
    | (true, false, false), b => h_5 b
    | (true, false, true), b => h_6 b
    | (true, true, c), x => h_7 c x) =
    h_4 x
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_5`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_5 : ∀
  (motive : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) (b : Bool)
  (h_1 : (b : Bool) → motive (false, false, false) b) (h_2 : (b : Bool) → motive (false, false, true) b)
  (h_3 : (x : Bool) → motive (false, true, false) x) (h_4 : (x : Bool) → motive (false, true, true) x)
  (h_5 : (b : Bool) → motive (true, false, false) b) (h_6 : (b : Bool) → motive (true, false, true) b)
  (h_7 : (c x : Bool) → motive (true, true, c) x),
  (match (true, false, false), b with
    | (false, false, false), b => h_1 b
    | (false, false, true), b => h_2 b
    | (false, true, false), x => h_3 x
    | (false, true, true), x => h_4 x
    | (true, false, false), b => h_5 b
    | (true, false, true), b => h_6 b
    | (true, true, c), x => h_7 c x) =
    h_5 b
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_6`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_6 : ∀
  (motive : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) (b : Bool)
  (h_1 : (b : Bool) → motive (false, false, false) b) (h_2 : (b : Bool) → motive (false, false, true) b)
  (h_3 : (x : Bool) → motive (false, true, false) x) (h_4 : (x : Bool) → motive (false, true, true) x)
  (h_5 : (b : Bool) → motive (true, false, false) b) (h_6 : (b : Bool) → motive (true, false, true) b)
  (h_7 : (c x : Bool) → motive (true, true, c) x),
  (match (true, false, true), b with
    | (false, false, false), b => h_1 b
    | (false, false, true), b => h_2 b
    | (false, true, false), x => h_3 x
    | (false, true, true), x => h_4 x
    | (true, false, false), b => h_5 b
    | (true, false, true), b => h_6 b
    | (true, true, c), x => h_7 c x) =
    h_6 b
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.eq_7 : ∀
  (motive : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) (c x : Bool)
  (h_1 : (b : Bool) → motive (false, false, false) b) (h_2 : (b : Bool) → motive (false, false, true) b)
  (h_3 : (x : Bool) → motive (false, true, false) x) (h_4 : (x : Bool) → motive (false, true, true) x)
  (h_5 : (b : Bool) → motive (true, false, false) b) (h_6 : (b : Bool) → motive (true, false, true) b)
  (h_7 : (c x : Bool) → motive (true, true, c) x),
  (match (true, true, c), x with
    | (false, false, false), b => h_1 b
    | (false, false, true), b => h_2 b
    | (false, true, false), x => h_3 x
    | (false, true, true), x => h_4 x
    | (true, false, false), b => h_5 b
    | (true, false, true), b => h_6 b
    | (true, true, c), x => h_7 c x) =
    h_7 c x
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.splitter`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next.match_1.splitter : (motive :
    TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase → Bool → Sort u_1) →
  (x : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase) →
    (x_1 : Bool) →
      ((b : Bool) → motive (false, false, false) b) →
        ((b : Bool) → motive (false, false, true) b) →
          ((x : Bool) → motive (false, true, false) x) →
            ((x : Bool) → motive (false, true, true) x) →
              ((b : Bool) → motive (true, false, false) b) →
                ((b : Bool) → motive (true, false, true) b) → ((c x : Bool) → motive (true, true, c) x) → motive x x_1
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output : TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.Phase →
  Bool → List Bool
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_1 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (false, false, false) x =
    if x = true then [true, true] else [false, true]
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_2`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_2 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (false, false, true) x = []
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_3`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_3 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (false, true, false) x =
    List.replicate 4 x
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_4`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_4 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (false, true, true) x =
    List.replicate 4 x ++ [false, false, true, true]
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_5`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_5 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (true, false, false) x =
    if x = true then [] else [false, true]
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_6`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_6 : ∀
  (x : Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (true, false, true) x =
    if x = true then [true, true, true, true] else [false, false, true, true]
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output.eq_7 : ∀
  (x c : Bool), TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (true, true, c) x = []
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_argument`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_argument : ∀
  (n : ℕ) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (true, false, true)
      (List.replicate n true ++ false :: r) =
    Turing.dbl (Turing.dbl (List.replicate n true)) ++ [false, false, true, true] ++
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝¹
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝¹ (true, false, false) r
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_arguments`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_arguments : ∀
  (args : List ℕ) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (true, false, false)
      (BoolCircuit.encodeList BoolCircuit.encodeNat args ++ r) =
    Turing.dbl (Complexity.BinArith.encWords (List.map (fun a => List.replicate a true) args)) ++ [false, true] ++
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝¹
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝¹ (false, false, true) r
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_done`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_done : ∀
  (w : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (true, true, false) w =
    []
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_gate`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_gate : ∀
  (g : BoolCircuit.DAGGate) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (false, true, false)
      (g.encode ++ r) =
    Turing.dbl (TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord g) ++
        [false, true] ++
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝¹
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝¹ (false, false, true) r
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_gates`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_gates : ∀
  (gs : List BoolCircuit.DAGGate) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (false, false, true)
      (BoolCircuit.encodeList BoolCircuit.DAGGate.encode gs ++ r) =
    Complexity.BinArith.encWords
      (List.map TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.gateRecord gs)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_input`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.scan_input : ∀
  (n : ℕ) (r : List Bool),
  TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝ (false, false, false)
      (List.replicate n true ++ false :: r) =
    Turing.dbl (List.replicate n true) ++ [false, true] ++
      TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner.scan
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.next✝¹
        TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder.output✝¹ (false, false, true) r
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded.match_1.eq_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded.match_1.eq_1 : ∀
  {β : Type} (motive : Option β → Sort u_1) (h_1 : Unit → motive none) (h_2 : (b : β) → motive (some b)),
  (match none with
    | none => h_1 ()
    | some b => h_2 b) =
    h_1 ()
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded.match_1.eq_2`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded.match_1.eq_2 : ∀
  {β : Type} (motive : Option β → Sort u_1) (b : β) (h_1 : Unit → motive none) (h_2 : (b : β) → motive (some b)),
  (match some b with
    | none => h_1 ()
    | some b => h_2 b) =
    h_2 b
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded.match_1.splitter`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.firstTagged_encoded.match_1.splitter : {β :
    Type} →
  (motive : Option β → Sort u_1) → (x : Option β) → motive none → ((b : β) → motive (some b)) → motive x
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulatorFactory.0._proof_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulatorFactory.0._proof_7 : ∀
  (inputs : Complexity.PolyExpr) (circuit : (n : ℕ) → BoolCircuit.DAGCircuit (inputs.eval n)) (n : ℕ),
  ¬(circuit n).gates.length ≤ (circuit n).gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.keyList_small`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.keyList_small : ∀
  (args : List ℕ) (a : Fin args.length → Bool) (K : ℕ → Bool → List Bool),
  args.length ≤ 2 →
    Complexity.BinArith.encWords (List.ofFn fun t => K args[t] (a t)) =
      if args.length = 0 then []
      else
        if args.length = 1 then Turing.pairEncode (K (args.getD 0 0) ((List.ofFn a).getD 0 false)) []
        else
          Turing.pairEncode (K (args.getD 0 0) ((List.ofFn a).getD 0 false))
            (Turing.pairEncode (K (args.getD 1 0) ((List.ofFn a).getD 1 false)) [])
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.keyList_small._proof_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.keyList_small._proof_1 : ∀
  (args : List ℕ), ¬args.length ≤ args.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.keyList_small._proof_1_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling.keyList_small._proof_1_1 : ∀
  (args : List ℕ), args.length + 1 + 1 + 1 ≤ 2 → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridSecurity.0._proof_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridSecurity.0._proof_7 : ∀
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (n : ℕ),
  ¬(C n).gates.length ≤ (C n).gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateStepCases.0._proof_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateStepCases.0._proof_7 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SamplerEndpoints.0._proof_8`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SamplerEndpoints.0._proof_8 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SamplerEndpoints.0._proof_9`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SamplerEndpoints.0._proof_9 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs) (S : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedFields.0._proof_8`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedFields.0._proof_8 : ∀ {inputs : ℕ}
  (C : BoolCircuit.DAGCircuit inputs), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedLaw.0._proof_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedLaw.0._proof_7 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedLaw.0._proof_8`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedLaw.0._proof_8 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m) (S : ℕ), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedPlan.0._proof_7`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedPlan.0._proof_7 : ∀ {m : ℕ}
  (C : BoolCircuit.DAGCircuit m), ¬C.gates.length ≤ C.gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedStepSecurity.0._proof_8`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedStepSecurity.0._proof_8 : ∀
  {inputs : ℕ → ℕ} (C : (n : ℕ) → BoolCircuit.DAGCircuit (inputs n)) (n : ℕ),
  ¬(C n).gates.length ≤ (C n).gates.length → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.gateBound`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.gateBound : ∀
  {m : ℕ} (C : BoolCircuit.DAGCircuit m) (S : ℕ), C.size ≤ S → C.gates.length ≤ S
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.gateBound._proof_1_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.gateBound._proof_1_1 : ∀
  {m : ℕ} (C : BoolCircuit.DAGCircuit m) (S : ℕ), m + C.gates.length ≤ S → ¬C.gates.length ≤ S → False
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv : (n :
    ℕ) →
  (Fin (2 * n) → Bool) ≃ (Fin n → Bool) × (Fin n → Bool)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv._proof_1`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv._proof_1 : (1 +
    1).AtLeastTwo
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv_first`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv_first : ∀
  (n : ℕ) (q : Fin (2 * n) → Bool) (t : Fin n),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv✝ n) q).1 t =
    q ((finCongr ⋯).symm (Fin.castAdd n t))
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv_second`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv_second : ∀
  (n : ℕ) (q : Fin (2 * n) → Bool) (t : Fin n),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv✝ n) q).2 t =
    q ((finCongr ⋯).symm (Fin.natAdd n t))
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEquiv`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEquiv : {m :
    ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (S n : ℕ) →
      (hS : C.size ≤ S) →
        (Bool → Fin S → Fin n → Bool) ≃
          (Fin C.size → Bool → Fin n → Bool) ×
            ({ x //
                x ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding C S hS) } →
              Fin n → Bool)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEquiv_unused`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEquiv_unused : ∀
  {m : ℕ} (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hS : C.size ≤ S) (q : Bool → Fin S → Fin n → Bool)
  (x : { x // x ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding C S hS) }),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEquiv✝ C S n hS) q).2 x = q (↑x).1 (↑x).2
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEquiv_used`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEquiv_used : ∀
  {m : ℕ} (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hS : C.size ≤ S) (q : Bool → Fin S → Fin n → Bool) (w : Fin C.size)
  (b : Bool),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEquiv✝ C S n hS) q).1 w b = q b (Fin.castLE hS w)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEquiv`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEquiv : {m :
    ℕ} →
  (C : BoolCircuit.DAGCircuit m) →
    (S n : ℕ) →
      (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2) →
        (hS : C.size ≤ S) →
          (Fin S → Fin 4 → Fin (2 * n) → Bool) ≃
            ((i : Fin C.gates.length) → (Fin C.gates[↑i].args.length → Bool) → (Fin n → Bool) × (Fin n → Bool)) ×
              ({ x //
                  x ∉
                    Set.range
                      ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS) } →
                Fin (2 * n) → Bool)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEquiv_unused`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEquiv_unused : ∀
  {m : ℕ} (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (q : Fin S → Fin 4 → Fin (2 * n) → Bool)
  (x :
    { x // x ∉ Set.range ⇑(TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding C S hA hS) }),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEquiv✝ C S n hA hS) q).2 x = q (↑x).1 (↑x).2
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEquiv_used`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEquiv_used : ∀
  {m : ℕ} (C : BoolCircuit.DAGCircuit m) (S n : ℕ) (hA : ∀ (i : Fin C.gates.length), C.gates[↑i].args.length ≤ 2)
  (hS : C.size ≤ S) (q : Fin S → Fin 4 → Fin (2 * n) → Bool) (i : Fin C.gates.length)
  (a : Fin C.gates[↑i].args.length → Bool),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEquiv✝ C S n hA hS) q).1 i a =
    (TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.halfEquiv✝ n)
      (q (Fin.castLE ⋯ i)
        ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
            C.gates[↑i].args.length ⋯)
          a))
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.splitEmbedding`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.splitEmbedding : {ι
    κ : Type} →
  (e : ι ↪ κ) → (V : Type) → (κ → V) ≃ (ι → V) × ({ x // x ∉ Set.range ⇑e } → V)
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.splitEmbedding_unused`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.splitEmbedding_unused : ∀
  {ι κ : Type} (e : ι ↪ κ) (V : Type) (f : κ → V) (j : { x // x ∉ Set.range ⇑e }),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.splitEmbedding✝ e V) f).2 j = f ↑j
```

## `_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.splitEmbedding_used`

```lean
_private.TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues.0.TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.splitEmbedding_used : ∀
  {ι κ : Type} (e : ι ↪ κ) (V : Type) (f : κ → V) (i : ι),
  ((TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.splitEmbedding✝ e V) f).1 i = f (e i)
```
