# New declaration source headers

Headers retain their source namespace/section context. Fully elaborated stored signatures
(including implicit section variables) are in the axiom/closure probe logs.

## TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean · isFaninTwo_iff

```lean
theorem isFaninTwo_iff :
    C.IsFaninTwo ↔
      (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
        ∀ g ∈ C.gates, g.args.length ≤ 2
```

## TCSlib/Complexity/CircuitComplexity/Uniform.lean · encodeList_nil

```lean
theorem encodeList_nil {α : Type} (f : α → List Bool) :
    encodeList f [] = [false]
```

## TCSlib/Complexity/CircuitComplexity/Uniform.lean · encodeList_cons

```lean
theorem encodeList_cons {α : Type} (f : α → List Bool) (a : α) (as : List α) :
    encodeList f (a :: as) = true :: (f a ++ encodeList f as)
```

## TCSlib/Complexity/CircuitComplexity/Uniform.lean · GateKind.encode_and

```lean
theorem GateKind.encode_and : GateKind.encode .and = [false, false]
```

## TCSlib/Complexity/CircuitComplexity/Uniform.lean · GateKind.encode_or

```lean
theorem GateKind.encode_or : GateKind.encode .or = [false, true]
```

## TCSlib/Complexity/CircuitComplexity/Uniform.lean · GateKind.encode_not

```lean
theorem GateKind.encode_not : GateKind.encode .not = [true, false]
```

## TCSlib/Complexity/CircuitComplexity/Uniform.lean · DAGGate.encode_eq

```lean
theorem DAGGate.encode_eq (g : DAGGate) :
    g.encode = g.kind.encode ++ encodeList encodeNat g.args
```

## TCSlib/Complexity/CircuitComplexity/Uniform.lean · DAGCircuit.encode_parts

```lean
theorem DAGCircuit.encode_parts {n : ℕ} (C : DAGCircuit n) :
    C.encode = encodeNat n ++ (encodeList DAGGate.encode C.gates ++ encodeNat C.output)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceProgram.lean · selectedKeys_poly

```lean
theorem selectedKeys_poly (width bound count inputs : List Bool → ℕ)
    (xs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hxs : PolyTimeComputable xs) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hcount_le : ∀ z, count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun v : Fin (count z) =>
      List.ofFn (keyAt (C z) (s z) v ((xs z).getD v false)))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceProgram.lean · outputPairs_poly

```lean
theorem outputPairs_poly (width bound count inputs : List Bool → ℕ)
    (description coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (count z) → ℕ)
    (houtsWord : ∀ z, pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)))
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j : Fin (count z) =>
      pairEncode (List.ofFn (keyAt (C z) (s z) (output z j) false))
        (List.ofFn (keyAt (C z) (s z) (output z j) true)))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceProgram.lean · message_poly

```lean
theorem message_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs inA outLen : List Bool → ℕ)
    (description xs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hinA : PolyTimeComputable fun z => List.replicate (inA z) true)
    (houtLen : PolyTimeComputable fun z => List.replicate (outLen z) true)
    (hdescription : PolyTimeComputable description) (hxs : PolyTimeComputable xs)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (outLen z) → ℕ)
    (hshape : ∀ z, description z = pairEncode (C z).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (output z j))))
    (hinA_le : ∀ z, inA z ≤ inputs z)
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => pairEncode
      (BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)))
      (pairEncode
        (BinArith.encWords (List.ofFn fun v : Fin (inA z) =>
          List.ofFn (keyAt (C z) (s z) v ((xs z).getD v false))))
        (BinArith.encWords (List.ofFn fun j : Fin (outLen z) =>
          pairEncode (List.ofFn (keyAt (C z) (s z) (output z j) false))
            (List.ofFn (keyAt (C z) (s z) (output z j) true)))))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · raw

```lean
def raw (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · raw_eq

```lean
theorem raw_eq (z : List Bool) :
    raw z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairEncode (pairFstD (NUPPT.inArg z)) []))
        (pairEncode (NUPPT.inCoins z) (Strategy.encodeMsgs [pairSndD (NUPPT.inArg z)]))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · polyTimeComputable_raw

```lean
theorem polyTimeComputable_raw : PolyTimeComputable raw
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · simulator

```lean
noncomputable def simulator (coins : PolyExpr) : NUPPT
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · simulator_eq

```lean
theorem simulator_eq (coins : PolyExpr) :
    simulator coins = NUPPT.ofPolyTimeUniform polyTimeComputable_raw coins
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · simulator_uniform

```lean
theorem simulator_uniform (coins : PolyExpr) : (simulator coins).Uniform
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · simulator_coins

```lean
theorem simulator_coins (coins : PolyExpr) : (simulator coins).coins = coins
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · simulator_runAtL

```lean
theorem simulator_runAtL (coins : PolyExpr) (n : ℕ) (x f r : List Bool) :
    (simulator coins).runAtL n (pairEncode x f) r =
      (⟨List.replicate n true, pairEncode x [], r, [f]⟩ : View).encode
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · statClose_real_ideal

```lean
theorem statClose_real_ideal (coins : PolyExpr) (F : Functionality) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
    {σ τ : Type*} [Fintype σ] [Fintype τ] [Nonempty τ]
    (e : σ ≃ (simulator coins).Coins n) (real : σ × τ → List Bool)
    (Bad : σ → Prop) (δ : ℝ) (hBad : uprob Bad ≤ δ)
    (hReal : ∀ r, ¬ Bad r.1 → real r =
      pairEncode (⟨List.replicate n true, pairEncode (List.ofFn x) [],
        List.ofFn (e r.1), [List.ofFn (F.f n x y).1]⟩ : View).encode
        (List.ofFn (F.f n x y).2)) :
    StatClose real (F.idealA (simulator coins) n x y) δ
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceSimulator.lean · distAdv_real_ideal_le

```lean
theorem distAdv_real_ideal_le (coins : PolyExpr) (F : Functionality) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
    {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Nonempty τ] [Fintype ρ]
    (e : σ ≃ (simulator coins).Coins n) (real : σ × τ → List Bool)
    (Bad : σ → Prop) (δ : ℝ) (hBad : uprob Bad ≤ δ)
    (hReal : ∀ r, ¬ Bad r.1 → real r =
      pairEncode (⟨List.replicate n true, pairEncode (List.ofFn x) [],
        List.ofFn (e r.1), [List.ofFn (F.f n x y).1]⟩ : View).encode
        (List.ofFn (F.f n x y).2)) (D : List Bool → ρ → Bool) :
    distAdv real (F.idealA (simulator coins) n x y) D ≤ δ
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceStatistical.lean · distAdv_real_ideal_le

```lean
theorem distAdv_real_ideal_le (H : HybridProtocol otFunctionality) (F : Functionality)
    (p : PolyExpr) (hCoins : H.main.P.coins = p)
    (hRounds : H.main.rounds = .const 2) (hFirst : H.main.verifierFirst = false)
    (BadWord : ℕ → List Bool → Prop) (δ : ℕ → ℝ)
    (hBad : ∀ n, uprob (fun r : Fin (p.eval n) → Bool => BadWord n (List.ofFn r)) ≤ δ n)
    (hOutputs : ∀ n x y, List.ofFn (F.f n x y).1 = List.ofFn (F.f n x y).2)
    (hCorrect : ∀ n x y (r : H.Coins n), ¬ BadWord n (List.ofFn r.1) →
      H.main.outV H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r =
          List.ofFn (F.f n x y).2) :
    ∀ (D : NUPPT) n x y,
      distAdv (H.realA F n x y) (F.idealA (AliceSimulator.simulator p) n x y)
        (D.distinguisherL n) ≤ δ n
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AllTables.lean · entryWord

```lean
noncomputable def entryWord (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AllTables.lean · entryWord_eq

```lean
theorem entryWord_eq (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (w : List Bool) :
    entryWord E₁ E₂ width bound inputs gates coins w =
      let record
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AllTables.lean · entryWord_poly

```lean
theorem entryWord_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs : List Bool → ℕ}
    {gates coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgates : PolyTimeComputable gates) (hcoins : PolyTimeComputable coins) :
    PolyTimeComputable (entryWord E₁ E₂ width bound inputs gates coins)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AllTables.lean · allTablesWord

```lean
noncomputable def allTablesWord (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AllTables.lean · allTablesWord_eq

```lean
theorem allTablesWord_eq (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (z : List Bool) :
    allTablesWord E₁ E₂ width bound inputs gates coins z =
      BinArith.encWords ((List.range (BinArith.decWords (gates z)).length).map fun i =>
        entryWord E₁ E₂ width bound inputs gates coins (pairEncode (List.replicate i true) z))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AllTables.lean · allTablesWord_poly

```lean
theorem allTablesWord_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs : List Bool → ℕ}
    {gates coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgates : PolyTimeComputable gates) (hcoins : PolyTimeComputable coins) :
    PolyTimeComputable (allTablesWord E₁ E₂ width bound inputs gates coins)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AllTables.lean · allTablesWord_garbledTables

```lean
theorem allTablesWord_garbledTables (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (gateCode : DAGGate → List Bool) (z : List Bool) (C : DAGCircuit (inputs z))
    (s : GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hgates : gates z = BinArith.encWords (C.gates.map gateCode))
    (hentry : ∀ i : Fin C.gates.length,
      entryWord E₁ E₂ width bound inputs gates coins (pairEncode (List.replicate i true) z) =
        BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) C s i)) :
    allTablesWord E₁ E₂ width bound inputs gates coins z =
      BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) C s i))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AllTables.lean · entryWord_pair

```lean
theorem entryWord_pair (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (i : ℕ) (z : List Bool) :
    entryWord E₁ E₂ width bound inputs gates coins (pairEncode (List.replicate i true) z) =
      TablesFromCoins.tableWord E₁ E₂ width bound inputs (fun _ => i)
        (fun v => pairFstD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
        (fun v => pairSndD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
        coins z
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputBit

```lean
def outputBit (z : List Bool) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputBit_eq

```lean
theorem outputBit_eq (z : List Bool) :
    outputBit z =
      let ctx
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputWord

```lean
def outputWord (p : PolyExpr) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputWord_eq

```lean
theorem outputWord_eq (p : PolyExpr) (z : List Bool) :
    outputWord p z = List.ofFn fun j : Fin (p.eval (pairFstD z).length) =>
      outputBit (pairEncode z (List.replicate j true))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputBit_poly

```lean
theorem outputBit_poly : PolyTimeComputable fun z => [outputBit z]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · length_outputWord

```lean
theorem length_outputWord (p : PolyExpr) (z : List Bool) :
    (outputWord p z).length = p.eval (pairFstD z).length
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputWord_getD

```lean
theorem outputWord_getD (p : PolyExpr) (z : List Bool) (j : ℕ) :
    (outputWord p z).getD j false =
      if j < p.eval (pairFstD z).length then
        outputBit (pairEncode z (List.replicate j true)) else false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputWord_poly

```lean
theorem outputWord_poly (p : PolyExpr) : PolyTimeComputable (outputWord p)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputBit_layout

```lean
theorem outputBit_layout {n k : ℕ} (vs : List (Fin n → Bool)) (ps : List (List Bool))
    (outs : Fin k → ℕ) (j : Fin k) (hv : outs j < vs.length) :
    outputBit (pairEncode
        (pairEncode (List.replicate n true) (pairEncode (BinArith.encWords (vs.map List.ofFn))
          (pairEncode (BinArith.encWords ps)
            (BinArith.encWords (List.ofFn fun i => BoolCircuit.encodeNat (outs i))))))
        (List.replicate j true)) =
      if List.ofFn (vs.getD (outs j) default) = pairFstD (ps.getD j []) then false
      else decide (List.ofFn (vs.getD (outs j) default) = pairSndD (ps.getD j []))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean · outputWord_layout

```lean
theorem outputWord_layout (p : PolyExpr) {n : ℕ} (vs : List (Fin n → Bool))
    (ps : List (List Bool)) (outs : Fin (p.eval n) → ℕ)
    (hv : ∀ j, outs j < vs.length) :
    outputWord p
        (pairEncode (List.replicate n true) (pairEncode (BinArith.encWords (vs.map List.ofFn))
          (pairEncode (BinArith.encWords ps)
            (BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (outs j)))))) =
      List.ofFn fun j =>
        if List.ofFn (vs.getD (outs j) default) = pairFstD (ps.getD j []) then false
        else decide (List.ofFn (vs.getD (outs j) default) = pairSndD (ps.getD j []))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobInit.lean · initEntry

```lean
def initEntry (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobInit.lean · initEntry_eq

```lean
theorem initEntry_eq (z : List Bool) :
    initEntry z =
      let ctx
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobInit.lean · initWords

```lean
def initWords (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobInit.lean · initWords_eq

```lean
theorem initWords_eq (z : List Bool) :
    initWords z = BinArith.encWords
      ((List.range ((pairFstD (pairSndD z)).length +
        (pairFstD (pairSndD (pairSndD z))).length)).map fun v =>
          initEntry (pairEncode (List.replicate v true) z))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobInit.lean · initEntry_poly

```lean
theorem initEntry_poly : PolyTimeComputable initEntry
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobInit.lean · initWords_poly

```lean
theorem initWords_poly : PolyTimeComputable initWords
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobInit.lean · initEntry_layout

```lean
theorem initEntry_layout (N A B msg ans : List Bool) (v : ℕ) :
    initEntry (pairEncode (List.replicate v true)
        (pairEncode N (pairEncode A (pairEncode B (pairEncode msg ans))))) =
      if v < A.length then
        List.ofFn (padFin N.length
          ((BinArith.decWords (pairFstD (pairSndD msg))).getD v []))
      else List.ofFn fun t : Fin N.length =>
        ans.getD ((v - A.length) * N.length + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobInit.lean · initWords_layout

```lean
theorem initWords_layout (N A B msg ans : List Bool) :
    initWords (pairEncode N (pairEncode A (pairEncode B (pairEncode msg ans)))) =
      BinArith.encWords (List.ofFn fun v : Fin (A.length + B.length) =>
        if (v : ℕ) < A.length then
          List.ofFn (padFin N.length
            ((BinArith.decWords (pairFstD (pairSndD msg))).getD v []))
        else List.ofFn fun t : Fin N.length =>
          ans.getD (((v : ℕ) - A.length) * N.length + t) false)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobProgram.lean · output_poly

```lean
theorem output_poly (inA inB outLen : PolyExpr)
    (circ : ∀ n, DAGCircuit (inA.eval n + inB.eval n))
    (outs : ∀ n, Fin (outLen.eval n) → ℕ)
    (houts : ∀ n j, outs n j < (circ n).size)
    {gen E₁ E₂ N msg ans : List Bool → List Bool}
    (hgen : PolyTimeComputable gen)
    (hgen_eq : ∀ n, gen (List.replicate n true) =
      pairEncode (circ n).encode
        (BinArith.encWords (List.ofFn fun j => encodeNat (outs n j))))
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hN : PolyTimeComputable N) (hmsg : PolyTimeComputable msg)
    (hans : PolyTimeComputable ans)
    (init : ∀ z, List (Fin (N z).length → Bool))
    (T : List Bool → ℕ → List (List Bool)) (pairs : List Bool → List (List Bool))
    (hinit : ∀ z, BinArith.encWords ((init z).map List.ofFn) =
      BobInit.initWords (pairEncode (List.replicate (N z).length true)
        (pairEncode (List.replicate (inA.eval (N z).length) true)
          (pairEncode (List.replicate (inB.eval (N z).length) true)
            (pairEncode (msg z) (ans z))))))
    (hinit_length : ∀ z, (init z).length = inA.eval (N z).length + inB.eval (N z).length)
    (hT : ∀ z v, T z v =
      if inA.eval (N z).length + inB.eval (N z).length ≤ v then
        BinArith.decWords ((BinArith.decWords (pairFstD (msg z))).getD
          (v - (inA.eval (N z).length + inB.eval (N z).length)) []) else [])
    (hpairs : ∀ z, pairs z = BinArith.decWords (pairSndD (pairSndD (msg z)))) :
    PolyTimeComputable fun z =>
      let vals
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · raw

```lean
def raw (fakeMessage activeAnswers : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · raw_eq

```lean
theorem raw_eq (fakeMessage activeAnswers : List Bool → List Bool) (z : List Bool) :
    raw fakeMessage activeAnswers z =
      (⟨NUPPT.inParam z, pairEncode (pairFstD (NUPPT.inArg z)) (activeAnswers z),
        [], [fakeMessage z]⟩ : View).encode
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · raw_poly

```lean
theorem raw_poly {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers) :
    PolyTimeComputable (raw fakeMessage activeAnswers)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · simulator

```lean
noncomputable def simulator {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) : NUPPT
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · simulator_eq

```lean
theorem simulator_eq {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) :
    simulator hM hA coins = NUPPT.ofPolyTimeUniform (raw_poly hM hA) coins
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · simulator_uniform

```lean
theorem simulator_uniform {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) : (simulator hM hA coins).Uniform
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · simulator_coins

```lean
theorem simulator_coins {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) : (simulator hM hA coins).coins = coins
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · simulator_runAtL

```lean
theorem simulator_runAtL {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) (n : ℕ) (y f r : List Bool) :
    (simulator hM hA coins).runAtL n (pairEncode y f) r =
      let w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · simulator_runAt

```lean
theorem simulator_runAt {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) (n : ℕ) (y f : List Bool) (r : (simulator hM hA coins).Coins n) :
    (simulator hM hA coins).runAt n (pairEncode y f) r =
      let w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobSimulator.lean · idealB_eq

```lean
theorem idealB_eq {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) (F : Functionality) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
    (r : (simulator hM hA coins).Coins n) :
    F.idealB (simulator hM hA coins) n x y r =
      let w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobTables.lean · tableSelector

```lean
def tableSelector (m msg : List Bool → List Bool) (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobTables.lean · tableSelector_eq

```lean
theorem tableSelector_eq (m msg : List Bool → List Bool) (w : List Bool) :
    tableSelector m msg w =
      let x
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobTables.lean · tableSelector_poly

```lean
theorem tableSelector_poly {m msg : List Bool → List Bool}
    (hm : PolyTimeComputable m) (hmsg : PolyTimeComputable msg) :
    PolyTimeComputable (tableSelector m msg)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobTables.lean · tableSelector_host

```lean
theorem tableSelector_host {α : Type} (m msg : List Bool → List Bool)
    (x gate : List Bool) (vs : List α) (code : α → List Bool) :
    tableSelector m msg (pairEncode x
        (pairEncode gate (BinArith.encWords (vs.map code)))) =
      BinArith.encWords (if (m x).length ≤ vs.length then
        BinArith.decWords ((BinArith.decWords (pairFstD (msg x))).getD
          (vs.length - (m x).length) []) else [])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobViewShape.lean · encode_viewV_eq

```lean
theorem encode_viewV_eq (H : HybridProtocol otFunctionality)
    (first : ℕ → List Bool → List Bool → List Bool)
    (hRounds : H.main.rounds = .const 2) (hFirst : H.main.verifierFirst = false)
    (hBobCoins : H.main.V.coins = .const 0)
    (hSender : ∀ w z r, H.main.P.next w z r [] = first w.length (pairFstD z) r)
    (n : ℕ) (xs ys : List Bool) (r : H.Coins n) :
    (H.main.viewV (List.replicate n true)
      (H.privA n xs ys (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n xs ys (List.ofFn r.1) (List.ofFn r.2)) r).encode =
      (⟨List.replicate n true,
        pairEncode ys (H.answersB n xs ys (List.ofFn r.1) (List.ofFn r.2)), [],
        [first n xs (List.ofFn r.1)]⟩ : View).encode
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CallEquations.lean · inputA_eq

```lean
theorem inputA_eq (A S : PolyExpr) (n m : ℕ) (x r : List Bool)
    (call : Fin (m * n) → Fin 2 → Bool)
    (hcall : ∀ (i : Fin m) (t : Fin n) (c : Fin 2),
      call (finProdFinEquiv (i, t)) c =
        r.getD (((decide ((c : ℕ) = 1)).toNat * S.eval n + A.eval n + i) * n + t) false)
    (j : Fin (m * n)) :
    OTInputs.otInputA A S (pairEncode (List.replicate n true)
      (pairEncode x (pairEncode r (List.replicate j true)))) = List.ofFn (call j)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CallEquations.lean · inputB_eq

```lean
theorem inputB_eq (n m : ℕ) (x r : List Bool)
    (call : Fin (m * n) → Fin 1 → Bool)
    (hcall : ∀ (i : Fin m) (t : Fin n) (c : Fin 1),
      call (finProdFinEquiv (i, t)) c = x.getD i false)
    (j : Fin (m * n)) :
    OTInputs.otInputB (pairEncode (List.replicate n true)
      (pairEncode x (pairEncode r (List.replicate j true)))) = List.ofFn (call j)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · Phase

```lean
abbrev Phase
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · phaseCode

```lean
def phaseCode (q : Phase) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · phaseCode_eq

```lean
theorem phaseCode_eq (q : Phase) : phaseCode q = [q.1, q.2.1, q.2.2]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · length_phaseCode

```lean
theorem length_phaseCode (q : Phase) : (phaseCode q).length = 3
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · readPhase

```lean
def readPhase (w : List Bool) : Phase
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · readPhase_eq

```lean
theorem readPhase_eq (w : List Bool) :
    readPhase w = (w.headD false, (w.drop 1).headD false, (w.drop 2).headD false)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · readPhase_code

```lean
theorem readPhase_code (q : Phase) : readPhase (phaseCode q) = q
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · scan

```lean
def scan (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) :
    Phase → List Bool → List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · scan_nil

```lean
theorem scan_nil (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    scan δ o q [] = []
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · scan_cons

```lean
theorem scan_cons (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase)
    (b : Bool) (w : List Bool) :
    scan δ o q (b :: w) = o q b ++ scan δ o (δ q b) w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · step

```lean
def step (δ : Phase → Bool → Phase) (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · step_eq

```lean
theorem step_eq (δ : Phase → Bool → Phase) (w : List Bool) :
    step δ w =
      pairEncode (phaseCode (δ (readPhase (pairFstD w)) ((pairSndD w).headD false)))
        ((pairSndD w).drop 1)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · emit

```lean
def emit (o : Phase → Bool → List Bool) (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · emit_eq

```lean
theorem emit_eq (o : Phase → Bool → List Bool) (w : List Bool) :
    emit o w =
      if pairSndD w = [] then []
      else o (readPhase (pairFstD w)) ((pairSndD w).headD false)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · table4_poly

```lean
private theorem table4_poly (F : Bool → Bool → Bool → Bool → List Bool)
    {a b c d : List Bool → Bool}
    (ha : PolyTimeComputable fun w => [a w])
    (hb : PolyTimeComputable fun w => [b w])
    (hc : PolyTimeComputable fun w => [c w])
    (hd : PolyTimeComputable fun w => [d w]) :
    PolyTimeComputable fun w => F (a w) (b w) (c w) (d w)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · phase_eq

```lean
theorem phase_eq : Phase = (Bool × Bool × Bool)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · step_poly

```lean
theorem step_poly (δ : Phase → Bool → Phase) : PolyTimeComputable (step δ)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · emit_poly

```lean
theorem emit_poly (o : Phase → Bool → List Bool) : PolyTimeComputable (emit o)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · step_pair

```lean
theorem step_pair (δ : Phase → Bool → Phase) (q : Phase) (w : List Bool) :
    step δ (pairEncode (phaseCode q) w) =
      pairEncode (phaseCode (δ q (w.headD false))) (w.drop 1)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · emit_pair

```lean
theorem emit_pair (o : Phase → Bool → List Bool) (q : Phase) (w : List Bool) :
    emit o (pairEncode (phaseCode q) w) =
      if w = [] then [] else o q (w.headD false)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · length_snd_step

```lean
theorem length_snd_step (δ : Phase → Bool → Phase) (w : List Bool) :
    (pairSndD (step δ w)).length ≤ (pairSndD w).length
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · length_snd_iterate

```lean
theorem length_snd_iterate (δ : Phase → Bool → Phase) (w : List Bool) (i : ℕ) :
    (pairSndD ((step δ)^[i] w)).length ≤ w.length
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · length_iterate

```lean
theorem length_iterate (δ : Phase → Bool → Phase) (w : List Bool) (i : ℕ) :
    ((step δ)^[i] w).length ≤ 9 * (w.length + 1)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · flatMap_scan

```lean
theorem flatMap_scan (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool)
    (N : ℕ) (q : Phase) (w : List Bool) (hN : w.length ≤ N) :
    (List.range N).flatMap
        (fun i => emit o ((step δ)^[i] (pairEncode (phaseCode q) w))) =
      scan δ o q w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · scan_poly

```lean
theorem scan_poly (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    PolyTimeComputable (scan δ o q)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean · scan_host

```lean
theorem scan_host (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    ∃ (M : FinTM Bool) (A d : ℕ),
      ModuleHost.Clean M (scan δ o q) (fun _ => []) (fun n => A * (n + 1) ^ d) ∧
      ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinGarbling.lean · keyWord_poly

```lean
theorem keyWord_poly {coins : List Bool → List Bool} {width bound vertex : List Bool → ℕ}
    {bit : List Bool → Bool} {key : ∀ z, Fin (width z) → Bool}
    (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hvertex : PolyTimeComputable fun z => List.replicate (vertex z) true)
    (hbit : PolyTimeComputable fun z => [bit z])
    (hkey : ∀ z t, key z t =
      (coins z).getD (((bit z).toNat * bound z + vertex z) * width z + t) false) :
    PolyTimeComputable fun z => List.ofFn (key z)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinGarbling.lean · assignmentIndex_poly

```lean
theorem assignmentIndex_poly {b₀ b₁ : List Bool → Bool}
    (h₀ : PolyTimeComputable fun z => [b₀ z])
    (h₁ : PolyTimeComputable fun z => [b₁ z]) :
    PolyTimeComputable fun z =>
      List.replicate ((b₀ z).toNat + 2 * (b₁ z).toNat) true
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinGarbling.lean · rowCoinWord_poly

```lean
theorem rowCoinWord_poly {coins : List Bool → List Bool}
    {width bound gate index : List Bool → ℕ} {nonce : ∀ z, Fin (width z) → Bool}
    (half : Bool) (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hindex : PolyTimeComputable fun z => List.replicate (index z) true)
    (hnonce : ∀ z t, nonce z t =
      (coins z).getD (2 * bound z * width z + (4 * gate z + index z) * (2 * width z) +
        half.toNat * width z + t) false) :
    PolyTimeComputable fun z => List.ofFn (nonce z)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinGarbling.lean · shiftBit_poly

```lean
theorem shiftBit_poly {coins : List Bool → List Bool} {width bound gate : List Bool → ℕ}
    (j : ℕ) (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true) :
    PolyTimeComputable fun z =>
      [(coins z).getD (10 * bound z * width z + 2 * gate z + j) false]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRead.lean · polyTimeComputable_window

```lean
theorem polyTimeComputable_window {w : List Bool → List Bool} {off len : List Bool → ℕ}
    (hw : PolyTimeComputable w)
    (hoff : PolyTimeComputable fun z => List.replicate (off z) true)
    (hlen : PolyTimeComputable fun z => List.replicate (len z) true) :
    PolyTimeComputable fun z =>
      List.ofFn (fun t : Fin (len z) => (w z).getD (off z + t) false)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · Blocks

```lean
abbrev Blocks (S n : ℕ)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · Blocks_eq

```lean
theorem Blocks_eq (S n : ℕ) :
    Blocks S n = ((Bool → Fin S → Fin n → Bool) ×
      (Fin S → Fin 4 → Fin (2 * n) → Bool) × (Fin S → Fin 2 → Bool))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · splitTape

```lean
def splitTape (S n : ℕ) :
    (Fin (10 * S * n + 2 * S) → Bool) ≃
      (Fin ((2 * S) * n) → Bool) ×
        (Fin ((S * 4) * (2 * n)) → Bool) × (Fin (S * 2) → Bool)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · splitTape_key

```lean
theorem splitTape_key (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin ((2 * S) * n)) :
    (splitTape S n r).1 i = (List.ofFn r).getD i false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · splitTape_row

```lean
theorem splitTape_row (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin ((S * 4) * (2 * n))) :
    (splitTape S n r).2.1 i = (List.ofFn r).getD (2 * S * n + i) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · splitTape_shift

```lean
theorem splitTape_shift (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin (S * 2)) :
    (splitTape S n r).2.2 i = (List.ofFn r).getD (10 * S * n + i) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · splitTape_eq

```lean
theorem splitTape_eq (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool) :
    splitTape S n r =
      ((fun i : Fin ((2 * S) * n) => (List.ofFn r).getD i false),
        (fun i : Fin ((S * 4) * (2 * n)) => (List.ofFn r).getD (2 * S * n + i) false),
        (fun i : Fin (S * 2) => (List.ofFn r).getD (10 * S * n + i) false))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · blocksEquiv

```lean
def blocksEquiv (S n : ℕ) : (Fin (10 * S * n + 2 * S) → Bool) ≃ Blocks S n
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · blocksEquiv_key

```lean
theorem blocksEquiv_key (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (b : Bool) (v : Fin S) (t : Fin n) :
    (blocksEquiv S n r).1 b v t =
      (List.ofFn r).getD ((b.toNat * S + v) * n + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · blocksEquiv_row

```lean
theorem blocksEquiv_row (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin S) (a : Fin 4) (t : Fin (2 * n)) :
    (blocksEquiv S n r).2.1 i a t =
      (List.ofFn r).getD (2 * S * n + (4 * i + a) * (2 * n) + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · blocksEquiv_shift

```lean
theorem blocksEquiv_shift (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin S) (t : Fin 2) :
    (blocksEquiv S n r).2.2 i t =
      (List.ofFn r).getD (10 * S * n + 2 * i + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · blocksEquiv_eq

```lean
theorem blocksEquiv_eq (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool) :
    blocksEquiv S n r =
      ((fun (b : Bool) (v : Fin S) (t : Fin n) =>
          (List.ofFn r).getD ((b.toNat * S + v) * n + t) false),
        (fun (i : Fin S) (a : Fin 4) (t : Fin (2 * n)) =>
          (List.ofFn r).getD (2 * S * n + (4 * i + a) * (2 * n) + t) false),
        (fun (i : Fin S) (t : Fin 2) =>
          (List.ofFn r).getD (10 * S * n + 2 * i + t) false))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · keyRelabel

```lean
def keyRelabel (S n : ℕ) (values : Fin S → Bool) :
    Equiv.Perm (Bool → Fin S → Fin n → Bool)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · keyRelabel_eq

```lean
theorem keyRelabel_eq (S n : ℕ) (values : Fin S → Bool)
    (k : Bool → Fin S → Fin n → Bool) (b : Bool) (v : Fin S) (t : Fin n) :
    keyRelabel S n values k b v t = k (xor b (values v)) v t
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · rowRelabel

```lean
def rowRelabel (S n : ℕ) (rows : Fin S → Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin S → Fin 4 → Fin (2 * n) → Bool)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · rowRelabel_eq

```lean
theorem rowRelabel_eq (S n : ℕ) (rows : Fin S → Equiv.Perm (Fin 4))
    (k : Fin S → Fin 4 → Fin (2 * n) → Bool) (i : Fin S) (a : Fin 4)
    (t : Fin (2 * n)) : rowRelabel S n rows k i a t = k i (rows i a) t
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · shiftRelabel

```lean
def shiftRelabel (S : ℕ) (mask : Fin S → Fin 2 → Bool) :
    Equiv.Perm (Fin S → Fin 2 → Bool)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · shiftRelabel_eq

```lean
theorem shiftRelabel_eq (S : ℕ) (mask : Fin S → Fin 2 → Bool)
    (k : Fin S → Fin 2 → Bool) (i : Fin S) (t : Fin 2) :
    shiftRelabel S mask k i t = xor (k i t) (mask i t)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · blockRelabel

```lean
def blockRelabel (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool) :
    Equiv.Perm (Blocks S n)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · blockRelabel_eq

```lean
theorem blockRelabel_eq (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool) (q : Blocks S n) :
    blockRelabel S n values rows mask q =
      (keyRelabel S n values q.1, rowRelabel S n rows q.2.1, shiftRelabel S mask q.2.2)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel

```lean
def relabel (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool) :
    Equiv.Perm (Fin (10 * S * n + 2 * S) → Bool)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_eq

```lean
theorem relabel_eq (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) :
    relabel S n values rows mask r =
      (blocksEquiv S n).symm (blockRelabel S n values rows mask (blocksEquiv S n r))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_blocks

```lean
theorem relabel_blocks (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) :
    blocksEquiv S n (relabel S n values rows mask r) =
      blockRelabel S n values rows mask (blocksEquiv S n r)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_key

```lean
theorem relabel_key (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n) :
    (blocksEquiv S n (relabel S n values rows mask r)).1 b v t =
      (blocksEquiv S n r).1 (xor b (values v)) v t
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_row

```lean
theorem relabel_row (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n)) :
    (blocksEquiv S n (relabel S n values rows mask r)).2.1 i a t =
      (blocksEquiv S n r).2.1 i (rows i a) t
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_shift

```lean
theorem relabel_shift (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2) :
    (blocksEquiv S n (relabel S n values rows mask r)).2.2 i t =
      xor ((blocksEquiv S n r).2.2 i t) (mask i t)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_key_getD

```lean
theorem relabel_key_getD (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n) :
    (List.ofFn (relabel S n values rows mask r)).getD ((b.toNat * S + v) * n + t) false =
      (List.ofFn r).getD (((xor b (values v)).toNat * S + v) * n + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_row_getD

```lean
theorem relabel_row_getD (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n)) :
    (List.ofFn (relabel S n values rows mask r)).getD
        (2 * S * n + (4 * i + a) * (2 * n) + t) false =
      (List.ofFn r).getD (2 * S * n + (4 * i + (rows i a : ℕ)) * (2 * n) + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_shift_getD

```lean
theorem relabel_shift_getD (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2) :
    (List.ofFn (relabel S n values rows mask r)).getD (10 * S * n + 2 * i + t) false =
      xor ((List.ofFn r).getD (10 * S * n + 2 * i + t) false) (mask i t)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_key_fixed

```lean
theorem relabel_key_fixed (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n)
    (hv : values v = false) :
    (List.ofFn (relabel S n values rows mask r)).getD ((b.toNat * S + v) * n + t) false =
      (List.ofFn r).getD ((b.toNat * S + v) * n + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_row_fixed

```lean
theorem relabel_row_fixed (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n))
    (ha : rows i a = a) :
    (List.ofFn (relabel S n values rows mask r)).getD
        (2 * S * n + (4 * i + a) * (2 * n) + t) false =
      (List.ofFn r).getD (2 * S * n + (4 * i + a) * (2 * n) + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean · relabel_shift_fixed

```lean
theorem relabel_shift_fixed (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2)
    (ht : mask i t = false) :
    (List.ofFn (relabel S n values rows mask r)).getD (10 * S * n + 2 * i + t) false =
      (List.ofFn r).getD (10 * S * n + 2 * i + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentFold_lt_four

```lean
theorem assignmentFold_lt_four {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 4
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentFold_lt_pow

```lean
theorem assignmentFold_lt_pow {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 2 ^ l
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentFold_injective

```lean
theorem assignmentFold_injective (l : ℕ) (hl : l ≤ 2) :
    Function.Injective (fun a : Fin l → Bool =>
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentEmbedding

```lean
def assignmentEmbedding (l : ℕ) (hl : l ≤ 2) : (Fin l → Bool) ↪ Fin 4
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentEmbedding_eq

```lean
theorem assignmentEmbedding_eq (l : ℕ) (hl : l ≤ 2) (a : Fin l → Bool) :
    (assignmentEmbedding l hl a : ℕ) =
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentEmbedding_lt_pow

```lean
theorem assignmentEmbedding_lt_pow (l : ℕ) (hl : l ≤ 2) (a : Fin l → Bool) :
    (assignmentEmbedding l hl a : ℕ) < 2 ^ l
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentPerm

```lean
def assignmentPerm (l : ℕ) (hl : l ≤ 2) (mask : Fin l → Bool) : Equiv.Perm (Fin 4)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentPerm_eq

```lean
theorem assignmentPerm_eq (l : ℕ) (hl : l ≤ 2) (mask : Fin l → Bool) :
    assignmentPerm l hl mask =
      (xorPerm mask).viaFintypeEmbedding (assignmentEmbedding l hl)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentPerm_code

```lean
theorem assignmentPerm_code (l : ℕ) (hl : l ≤ 2) (mask a : Fin l → Bool) :
    assignmentPerm l hl mask (assignmentEmbedding l hl a) =
      assignmentEmbedding l hl (xorPerm mask a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · assignmentPerm_unused

```lean
theorem assignmentPerm_unused (l : ℕ) (hl : l ≤ 2) (mask : Fin l → Bool)
    (a : Fin 4) (ha : 2 ^ l ≤ (a : ℕ)) : assignmentPerm l hl mask a = a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · keyMask

```lean
def keyMask {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (w : Fin S) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · keyMask_eq

```lean
theorem keyMask_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (w : Fin S) :
    keyMask C S v w = if (w : ℕ) < C.size then v w else false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · keyMask_vertex

```lean
theorem keyMask_vertex {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (hS : C.size ≤ S) (w : Fin C.size) :
    keyMask C S v (Fin.castLE hS w) = v w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · rowPerm

```lean
def rowPerm {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (v : ℕ → Bool) (i : Fin S) : Equiv.Perm (Fin 4)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · rowPerm_eq

```lean
theorem rowPerm_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (v : ℕ → Bool) (i : Fin S) :
    rowPerm C S hA v i =
      if hi : (i : ℕ) < C.gates.length then
        assignmentPerm (C.gates[(i : ℕ)]'hi).args.length (hA ⟨i, hi⟩)
          (RelabelGarbling.argValues C v ⟨i, hi⟩)
      else Equiv.refl _
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · rowPerm_gate

```lean
theorem rowPerm_gate {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length) :
    rowPerm C S hA v (Fin.castLE hG i) =
      assignmentPerm (C.gates[i]).args.length (hA i) (RelabelGarbling.argValues C v i)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · rowPerm_fold

```lean
theorem rowPerm_fold {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    (rowPerm C S hA v (Fin.castLE hG i)
        (assignmentEmbedding (C.gates[i]).args.length (hA i) a) : ℕ) =
      (List.ofFn (xorPerm (RelabelGarbling.argValues C v i) a)).foldr
        (fun b k => b.toNat + 2 * k) 0
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · shiftMask

```lean
def shiftMask {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (i : Fin S) (t : Fin 2) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · shiftMask_eq

```lean
theorem shiftMask_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (i : Fin S) (t : Fin 2) :
    shiftMask C S v i t =
      if hi : (i : ℕ) < C.gates.length then
        if ht : (t : ℕ) < (C.gates[(i : ℕ)]'hi).args.length then
          v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht)
        else false
      else false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · shiftMask_argument

```lean
theorem shiftMask_argument {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length)
    (t : Fin (C.gates[i]).args.length) :
    shiftMask C S v (Fin.castLE hG i) (Fin.castLE (hA i) t) =
      v ((C.gates[i]).args[t])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · keyMask_unused

```lean
theorem keyMask_unused {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (w : Fin S) (hw : C.size ≤ (w : ℕ)) : keyMask C S v w = false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · rowPerm_unused_gate

```lean
theorem rowPerm_unused_gate {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (i : Fin S) (hi : C.gates.length ≤ (i : ℕ)) :
    rowPerm C S hA v i = Equiv.refl _
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · rowPerm_unused_code

```lean
theorem rowPerm_unused_code {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (a : Fin 4)
    (ha : 2 ^ (C.gates[i]).args.length ≤ (a : ℕ)) :
    rowPerm C S hA v (Fin.castLE hG i) a = a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · shiftMask_unused_gate

```lean
theorem shiftMask_unused_gate {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (i : Fin S) (t : Fin 2) (hi : C.gates.length ≤ (i : ℕ)) :
    shiftMask C S v i t = false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · shiftMask_unused_argument

```lean
theorem shiftMask_unused_argument {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (t : Fin 2)
    (ht : (C.gates[i]).args.length ≤ (t : ℕ)) :
    shiftMask C S v (Fin.castLE hG i) t = false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · relabel_key_getD

```lean
theorem relabel_key_getD {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hS : C.size ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool)
    (w : Fin C.size) (b : Bool) (t : Fin n) :
    (List.ofFn (CoinRelabel.relabel S n (keyMask C S v)
      (rowPerm C S hA v) (shiftMask C S v) r)).getD
        ((b.toNat * S + w) * n + t) false =
      (List.ofFn r).getD (((xor b (v w)).toNat * S + w) * n + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · relabel_row_getD

```lean
theorem relabel_row_getD {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (t : Fin (2 * n)) :
    (List.ofFn (CoinRelabel.relabel S n (keyMask C S v)
      (rowPerm C S hA v) (shiftMask C S v) r)).getD
        (2 * S * n + (4 * i +
          (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false =
      (List.ofFn r).getD (2 * S * n + (4 * i +
        (List.ofFn (xorPerm (RelabelGarbling.argValues C v i) a)).foldr
          (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · relabel_shift_getD

```lean
theorem relabel_shift_getD {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin C.gates.length) (t : Fin (C.gates[i]).args.length) :
    (List.ofFn (CoinRelabel.relabel S n (keyMask C S v)
      (rowPerm C S hA v) (shiftMask C S v) r)).getD
        (10 * S * n + 2 * i + t) false =
      xor ((List.ofFn r).getD (10 * S * n + 2 * i + t) false)
        (v ((C.gates[i]).args[t]))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean · seed_relabel

```lean
theorem seed_relabel {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hS : C.size ≤ S)
    (seed : List Bool → GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (hK : ∀ q (w : Fin C.size) b (t : Fin n),
      (seed q).1 w b t = q.getD ((b.toNat * S + w) * n + t) false)
    (hR₀ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
        (t : Fin n),
      ((seed q).2.1 i a).1 t = q.getD (2 * S * n + (4 * i +
        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
    (hR₁ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
        (t : Fin n),
      ((seed q).2.1 i a).2 t = q.getD (2 * S * n + (4 * i +
        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
    (hP : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
        (t : Fin (C.gates[i]).args.length),
      (seed q).2.2 i a t = xor (a t) (q.getD (10 * S * n + 2 * i + t) false))
    (r : Fin (10 * S * n + 2 * S) → Bool) :
    seed (List.ofFn (CoinRelabel.relabel S n (keyMask C S v)
        (rowPerm C S hA v) (shiftMask C S v) r)) =
      RelabelGarbling.relabelSeed C v (seed (List.ofFn r))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoordinateSwap.lean · swap

```lean
@[simps (config := { isSimp := false })]
def swap (pick : P → I → Option J) (place : P → J → Option I)
    (s : (P × (I → V)) × (J → V)) : (P × (I → V)) × (J → V)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoordinateSwap.lean · swap_eq

```lean
theorem swap_eq (pick : P → I → Option J) (place : P → J → Option I)
    (s : (P × (I → V)) × (J → V)) :
    swap pick place s =
      ((s.1.1, fun i => (pick s.1.1 i).elim (s.1.2 i) (fun j => s.2 j)),
        fun j => (place s.1.1 j).elim (s.2 j) (fun i => s.1.2 i))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoordinateSwap.lean · swap_involutive

```lean
theorem swap_involutive (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i) :
    Function.Involutive (swap pick place : ((P × (I → V)) × (J → V)) → _)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoordinateSwap.lean · equiv

```lean
@[simps (config := { isSimp := false }) apply symm_apply]
def equiv (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i) :
    ((P × (I → V)) × (J → V)) ≃ ((P × (I → V)) × (J → V))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoordinateSwap.lean · equiv_apply_eq

```lean
theorem equiv_apply_eq (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i)
    (s : (P × (I → V)) × (J → V)) :
    equiv pick place hmatch s = swap pick place s
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoordinateSwap.lean · equiv_symm_apply_eq

```lean
theorem equiv_symm_apply_eq (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i)
    (s : (P × (I → V)) × (J → V)) :
    (equiv pick place hmatch).symm s = swap pick place s
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoordinateSwap.lean · acceptProb_swap

```lean
theorem acceptProb_swap [Fintype P] [Fintype I] [Fintype J] [Fintype V]
    [DecidableEq I] [DecidableEq J]
    [Nonempty (J → V)] {γ ρ : Type*} [Fintype ρ]
    (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i)
    (X : (P × (I → V)) → γ) (D : γ → ρ → Bool) :
    acceptProb (fun s : (P × (I → V)) × (J → V) => X (swap pick place s).1) D =
      acceptProb X D
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoordinateSwap.lean · acceptProb_fill

```lean
theorem acceptProb_fill [Fintype P] [Fintype I] [Fintype J] [Fintype V]
    [DecidableEq I] [DecidableEq J]
    {S T γ ρ : Type*} [Fintype S] [Fintype T] [Nonempty T] [Fintype ρ]
    (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i)
    (seedEquiv : S ≃ (P × (I → V))) (challengeEquiv : T ≃ (J → V))
    (fill : S → T → S)
    (hfill : ∀ s c, seedEquiv (fill s c) =
      (swap pick place (seedEquiv s, challengeEquiv c)).1)
    (X : S → γ) (D : γ → ρ → Bool) :
    acceptProb (fun z : S × T => X (fill z.1 z.2)) D = acceptProb X D
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · specialDecTagged

```lean
def specialDecTagged (E : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · specialDecTagged_eq

```lean
theorem specialDecTagged_eq (E : List Bool → List Bool) (z : List Bool) :
    specialDecTagged E z =
      match spDecStr E (pairFstD z).length (pairFstD (pairSndD z)).length
          (pairFstD (pairSndD (pairSndD z))) (pairSndD (pairSndD (pairSndD z))) with
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · specialDecTagged_poly

```lean
theorem specialDecTagged_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (specialDecTagged E)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · specialDecTagged_pairEncode

```lean
theorem specialDecTagged_pairEncode (E : List Bool → List Bool) (N L k c : List Bool) :
    specialDecTagged E (pairEncode N (pairEncode L (pairEncode k c))) =
      match spDecStr E N.length L.length k c with
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · bindTagged

```lean
def bindTagged (F : List Bool → List Bool) (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · bindTagged_eq

```lean
theorem bindTagged_eq (F : List Bool → List Bool) (w : List Bool) :
    bindTagged F w = if w = [] then [] else F (w.drop 1)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · bindTagged_option

```lean
theorem bindTagged_option (F : List Bool → List Bool) (o : Option (List Bool)) :
    bindTagged F (match o with | none => [] | some m => true :: m) =
      match o with
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · bindTagged_poly

```lean
theorem bindTagged_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (bindTagged F)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · checkFinTagged

```lean
def checkFinTagged (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · checkFinTagged_eq

```lean
theorem checkFinTagged_eq (z : List Bool) :
    checkFinTagged z = if pairSndD z = [] then []
      else if ((pairSndD z).drop 1).length = (pairFstD z).length then
        true :: (pairSndD z).drop 1 else []
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · checkFinTagged_option

```lean
theorem checkFinTagged_option (N : List Bool) (o : Option (List Bool)) :
    checkFinTagged (pairEncode N (match o with | none => [] | some m => true :: m)) =
      match o.bind (TCSlib.Cryptography.decodeFin N.length) with
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · checkFinTagged_poly

```lean
theorem checkFinTagged_poly : PolyTimeComputable checkFinTagged
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · nestedDecTagged

```lean
def nestedDecTagged (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · nestedDecTagged_eq

```lean
theorem nestedDecTagged_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    nestedDecTagged E₁ E₂ z =
  let N
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · nestedDecTagged_encoded

```lean
theorem nestedDecTagged_encoded (E₁ E₂ : List Bool → List Bool) (N : List Bool)
    (ks : List (Fin N.length → Bool)) (c : List Bool) :
    nestedDecTagged E₁ E₂
        (pairEncode N (pairEncode (BinArith.encWords (ks.map List.ofFn)) c)) =
      match (nestedSpecial E₁ E₂ N.length).dec ks c with
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Decryption.lean · nestedDecTagged_poly

```lean
theorem nestedDecTagged_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (nestedDecTagged E₁ E₂)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · next

```lean
private def next : Phase → Bool → Phase
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · output

```lean
private def output : Phase → Bool → List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · gateRecord

```lean
def gateRecord (g : DAGGate) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · gateRecord_eq

```lean
theorem gateRecord_eq (g : DAGGate) :
    gateRecord g =
      pairEncode g.kind.encode
        (BinArith.encWords (g.args.map fun a => List.replicate a true))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · readCircuit

```lean
def readCircuit (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · readCircuit_eq

```lean
theorem readCircuit_eq (w : List Bool) :
    readCircuit w = ChunkScanner.scan next output (false, false, false) w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · readCircuit_poly

```lean
theorem readCircuit_poly : PolyTimeComputable readCircuit
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · decodeDescription

```lean
def decodeDescription (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · decodeDescription_eq

```lean
theorem decodeDescription_eq (w : List Bool) :
    decodeDescription w = pairEncode (readCircuit (pairFstD w)) (pairSndD w)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · decodeDescription_poly

```lean
theorem decodeDescription_poly : PolyTimeComputable decodeDescription
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · dbl_pair

```lean
private theorem dbl_pair (a b : List Bool) :
    dbl (pairEncode a b) =
      dbl (dbl a) ++ [false, false, true, true] ++ dbl b
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · scan_done

```lean
private theorem scan_done (w : List Bool) :
    ChunkScanner.scan next output (true, true, false) w = []
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · scan_input

```lean
private theorem scan_input (n : ℕ) (r : List Bool) :
    ChunkScanner.scan next output (false, false, false)
        (List.replicate n true ++ false :: r) =
      dbl (List.replicate n true) ++ [false, true] ++
        ChunkScanner.scan next output (false, false, true) r
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · scan_argument

```lean
private theorem scan_argument (n : ℕ) (r : List Bool) :
    ChunkScanner.scan next output (true, false, true)
        (List.replicate n true ++ false :: r) =
      dbl (dbl (List.replicate n true)) ++ [false, false, true, true] ++
        ChunkScanner.scan next output (true, false, false) r
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · scan_arguments

```lean
private theorem scan_arguments (args : List ℕ) (r : List Bool) :
    ChunkScanner.scan next output (true, false, false) (encodeList encodeNat args ++ r) =
      dbl (BinArith.encWords (args.map fun a => List.replicate a true)) ++ [false, true] ++
        ChunkScanner.scan next output (false, false, true) r
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · scan_gate

```lean
private theorem scan_gate (g : DAGGate) (r : List Bool) :
    ChunkScanner.scan next output (false, true, false) (g.encode ++ r) =
      dbl (gateRecord g) ++ [false, true] ++
        ChunkScanner.scan next output (false, false, true) r
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · scan_gates

```lean
private theorem scan_gates (gs : List DAGGate) (r : List Bool) :
    ChunkScanner.scan next output (false, false, true) (encodeList DAGGate.encode gs ++ r) =
      BinArith.encWords (gs.map gateRecord)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · readCircuit_encode

```lean
theorem readCircuit_encode {n : ℕ} (C : DAGCircuit n) :
    readCircuit C.encode =
      pairEncode (List.replicate n true) (BinArith.encWords (C.gates.map gateRecord))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · decodeDescription_pair

```lean
theorem decodeDescription_pair {n : ℕ} (C : DAGCircuit n) (outs : List Bool) :
    decodeDescription (pairEncode C.encode outs) =
      pairEncode
        (pairEncode (List.replicate n true) (BinArith.encWords (C.gates.map gateRecord)))
        outs
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean · decodeDescription_host

```lean
theorem decodeDescription_host :
    ∃ (M : FinTM Bool) (A c : ℕ),
      ModuleHost.Clean M decodeDescription (fun _ => []) (fun n => A * (n + 1) ^ c) ∧
      (∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
        |(M.tm.runFrom
          (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
            (A * (arg.length + 1) ^ c : ℕ)) ∧
      ∀ (n : ℕ) (C : DAGCircuit n) (outs : List Bool),
        decodeDescription (pairEncode C.encode outs) =
          pairEncode
            (pairEncode (List.replicate n true) (BinArith.encWords (C.gates.map gateRecord)))
            outs
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · keyLookup

```lean
def keyLookup (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · keyLookup_eq

```lean
theorem keyLookup_eq (z : List Bool) :
    keyLookup z = EnsembleLemmas.padL (pairFstD (pairFstD z)).length
      (BinArith.getW (pairEncode (pairSndD z) (pairSndD (pairFstD z))))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · keyLookup_poly

```lean
theorem keyLookup_poly : PolyTimeComputable keyLookup
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · keyLookup_encoded

```lean
theorem keyLookup_encoded (N : List Bool) (vs : List (Fin N.length → Bool)) (a : ℕ) :
    keyLookup (pairEncode (pairEncode N (BinArith.encWords (vs.map List.ofFn)))
        (List.replicate a true)) = List.ofFn (vs.getD a default)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · argKeysCode

```lean
def argKeysCode (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · argKeysCode_eq

```lean
theorem argKeysCode_eq (z : List Bool) :
    argKeysCode z = BinArith.mapW keyLookup
      (pairEncode (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
        (pairSndD (pairSndD z)))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · argKeysCode_poly

```lean
theorem argKeysCode_poly : PolyTimeComputable argKeysCode
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · argKeysCode_encoded

```lean
theorem argKeysCode_encoded (N : List Bool) (vs : List (Fin N.length → Bool))
    (args : List ℕ) :
    argKeysCode (pairEncode N (pairEncode (BinArith.encWords (vs.map List.ofFn))
        (BinArith.encWords (args.map fun a => List.replicate a true)))) =
      BinArith.encWords ((args.map fun a => vs.getD a default).map List.ofFn)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · nestedRowTagged

```lean
def nestedRowTagged (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · nestedRowTagged_eq

```lean
theorem nestedRowTagged_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    nestedRowTagged E₁ E₂ z =
      nestedDecTagged E₁ E₂ (pairEncode (pairFstD (pairFstD z))
        (pairEncode (pairSndD (pairFstD z)) (pairSndD z)))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · nestedRowTagged_poly

```lean
theorem nestedRowTagged_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (nestedRowTagged E₁ E₂)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · untagDefault

```lean
def untagDefault (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · untagDefault_eq

```lean
theorem untagDefault_eq (z : List Bool) :
    untagDefault z = if pairSndD z = [] then List.replicate (pairFstD z).length false
      else (pairSndD z).drop 1
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · untagDefault_poly

```lean
theorem untagDefault_poly : PolyTimeComputable untagDefault
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · untagDefault_encoded

```lean
theorem untagDefault_encoded (N : List Bool) (o : Option (Fin N.length → Bool)) :
    untagDefault (pairEncode N (match o with | none => [] | some k => true :: List.ofFn k)) =
      List.ofFn (o.getD default)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · evalGateWord

```lean
noncomputable def evalGateWord (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · evalGateWord_eq

```lean
theorem evalGateWord_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    evalGateWord E₁ E₂ z =
  let N
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · evalGateWord_poly

```lean
theorem evalGateWord_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (evalGateWord E₁ E₂)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · evalGateWord_encoded

```lean
theorem evalGateWord_encoded (E₁ E₂ : List Bool → List Bool) (N : List Bool)
    (T : ℕ → List (List Bool)) (v : ℕ) (g : DAGGate)
    (vs : List (Fin N.length → Bool)) :
    evalGateWord E₁ E₂ (pairEncode N
        (pairEncode (BinArith.encWords (g.args.map fun a => List.replicate a true))
          (pairEncode (BinArith.encWords (vs.map List.ofFn)) (BinArith.encWords (T v))))) =
      List.ofFn (evalGate (nestedSpecial E₁ E₂ N.length) T v g vs)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · evalGateAppendWord

```lean
noncomputable def evalGateAppendWord (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · evalGateAppendWord_eq

```lean
theorem evalGateAppendWord_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    evalGateAppendWord E₁ E₂ z =
      pairFstD (pairSndD (pairSndD z)) ++ pairEncode (evalGateWord E₁ E₂ z) []
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · evalGateAppendWord_poly

```lean
theorem evalGateAppendWord_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (evalGateAppendWord E₁ E₂)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/EvalGate.lean · evalGateAppendWord_encoded

```lean
theorem evalGateAppendWord_encoded (E₁ E₂ : List Bool → List Bool) (N : List Bool)
    (T : ℕ → List (List Bool)) (v : ℕ) (g : DAGGate)
    (vs : List (Fin N.length → Bool)) :
    evalGateAppendWord E₁ E₂ (pairEncode N
        (pairEncode (BinArith.encWords (g.args.map fun a => List.replicate a true))
          (pairEncode (BinArith.encWords (vs.map List.ofFn)) (BinArith.encWords (T v))))) =
      BinArith.encWords ((vs ++ [evalGate (nestedSpecial E₁ E₂ N.length) T v g vs]).map
        List.ofFn)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeMessage.lean · message

```lean
noncomputable def message {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (result : Fin outLen → Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeMessage.lean · message_eq

```lean
theorem message_eq {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (result : Fin outLen → Bool) :
    message M C s inA outLen output result =
      pairEncode (BinArith.encWords (List.ofFn fun i => BinArith.encWords (table M C s i)))
        (pairEncode
          (BinArith.encWords (List.ofFn fun v : Fin inA => List.ofFn (keyAt C s v false)))
          (BinArith.encWords (List.ofFn fun j =>
            pairEncode (List.ofFn (decodePair C s (output j) (result j)).1)
              (List.ofFn (decodePair C s (output j) (result j)).2))))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeObjects.lean · row

```lean
def row (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) : Cipher
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeObjects.lean · row_eq

```lean
theorem row_eq (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    row M C s i a = M.enc (argKeys C s i a) (keyAt C s (inputs + i) false) (s.2.1 i a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeObjects.lean · table

```lean
noncomputable def table (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length) : List Cipher
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeObjects.lean · table_eq

```lean
theorem table_eq (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    table M C s i =
      (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map
        fun a => row M C s i (s.2.2 i a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeObjects.lean · decodePair

```lean
def decodePair (C : DAGCircuit inputs) (s : GarbleSeed C K ρ) (v : ℕ) (b : Bool) : K × K
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeObjects.lean · decodePair_eq

```lean
theorem decodePair_eq (C : DAGCircuit inputs) (s : GarbleSeed C K ρ) (v : ℕ) (b : Bool) :
    decodePair C s v b = (keyAt C s v b, keyAt C s v (!b))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeObjects.lean · activeAnswers

```lean
def activeAnswers {width : ℕ} (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) :
    Fin (count * width) → Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeObjects.lean · activeAnswers_eq

```lean
theorem activeAnswers_eq {width : ℕ} (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) (t : Fin (count * width)) :
    activeAnswers C s first count t = keyAt C s (first + t.divNat) false t.modNat
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean · activeAnswers_word

```lean
theorem activeAnswers_word {inputs width : ℕ} {ρ : Type} (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) :
    List.ofFn (FakeObjects.activeAnswers C s first count) =
      (List.ofFn fun i : Fin count => List.ofFn (keyAt C s (first + i) false)).flatten
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean · activeAnswers_poly

```lean
theorem activeAnswers_poly (width bound first count inputs : List Bool → ℕ)
    (coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hfirst : PolyTimeComputable fun z => List.replicate (first z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hrange : ∀ z, first z + count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z =>
      List.ofFn (FakeObjects.activeAnswers (C z) (s z) (first z) (count z))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean · swapPairs_poly

```lean
theorem swapPairs_poly (count : List Bool → ℕ) (pairs result : List Bool → List Bool)
    (value : ∀ z, Fin (count z) → List Bool × List Bool)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hpairs : PolyTimeComputable pairs) (hresult : PolyTimeComputable result)
    (hshape : ∀ z, pairs z = BinArith.encWords (List.ofFn fun j =>
      pairEncode (value z j).1 (value z j).2)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j =>
      if (result z).getD j false then pairEncode (value z j).2 (value z j).1
      else pairEncode (value z j).1 (value z j).2)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean · outputPairs_poly

```lean
theorem outputPairs_poly (width bound count inputs : List Bool → ℕ)
    (description coins result : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (hresult : PolyTimeComputable result) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (count z) → ℕ)
    (houtsWord : ∀ z, pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)))
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j : Fin (count z) =>
      pairEncode (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
        ((result z).getD j false)).1)
        (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
          ((result z).getD j false)).2))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean · inputKeys_poly

```lean
theorem inputKeys_poly (width bound count inputs : List Bool → ℕ)
    (coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hcount_le : ∀ z, count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun v : Fin (count z) =>
      List.ofFn (keyAt (C z) (s z) v false))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean · tables_poly

```lean
theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs : List Bool → ℕ)
    (description outs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hshape : ∀ z, description z = pairEncode (C z).encode (outs z))
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i =>
      BinArith.encWords (FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean · message_poly

```lean
theorem message_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs inA outLen : List Bool → ℕ)
    (description result coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hinA : PolyTimeComputable fun z => List.replicate (inA z) true)
    (houtLen : PolyTimeComputable fun z => List.replicate (outLen z) true)
    (hdescription : PolyTimeComputable description) (hresult : PolyTimeComputable result)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (outLen z) → ℕ)
    (hshape : ∀ z, description z = pairEncode (C z).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (output z j))))
    (hinA_le : ∀ z, inA z ≤ inputs z)
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => pairEncode
      (BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)))
      (pairEncode
        (BinArith.encWords (List.ofFn fun v : Fin (inA z) =>
          List.ofFn (keyAt (C z) (s z) v false)))
        (BinArith.encWords (List.ofFn fun j : Fin (outLen z) =>
          pairEncode
            (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
              ((result z).getD j false)).1)
            (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
              ((result z).getD j false)).2))))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · parameter

```lean
def parameter (z : List Bool) : ℕ
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · parameter_eq

```lean
theorem parameter_eq (z : List Bool) : parameter z = (NUPPT.inParam z).length
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · parameter_layout

```lean
theorem parameter_layout (n : ℕ) (arg advice coins : List Bool) :
    parameter (NUPPT.layout (List.replicate n true) arg advice coins) = n
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · Data

```lean
structure Data
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · Data.make

```lean
@[simps (config := { isSimp := false }) E₁ E₂ bound inputs inA inB outLen gen circuit output seed]
def Data.make : Data
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · description

```lean
def description (d : Data) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · description_eq

```lean
theorem description_eq (d : Data) (z : List Bool) :
    description d z = d.gen (List.replicate (parameter z) true)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · messageAt

```lean
noncomputable def messageAt (d : Data) (n : ℕ) (r f : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · messageAt_eq

```lean
theorem messageAt_eq (d : Data) (n : ℕ) (r f : List Bool) :
    messageAt d n r f =
      FakeObjects.message (nestedSpecial d.E₁ d.E₂ n) (d.circuit n) (d.seed n r)
        (d.inA.eval n) (d.outLen.eval n) (d.output n) (fun j => f.getD j false)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · answersAt

```lean
def answersAt (d : Data) (n : ℕ) (r : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · answersAt_eq

```lean
theorem answersAt_eq (d : Data) (n : ℕ) (r : List Bool) :
    answersAt d n r = List.ofFn (FakeObjects.activeAnswers (d.circuit n) (d.seed n r)
      (d.inA.eval n) (d.inB.eval n))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · message

```lean
noncomputable def message (d : Data) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · message_eq

```lean
theorem message_eq (d : Data) (z : List Bool) :
    message d z = messageAt d (parameter z) (NUPPT.inCoins z)
      (pairSndD (NUPPT.inArg z))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · answers

```lean
def answers (d : Data) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · answers_eq

```lean
theorem answers_eq (d : Data) (z : List Bool) :
    answers d z = answersAt d (parameter z) (NUPPT.inCoins z)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · parameter_unary_poly

```lean
theorem parameter_unary_poly :
    PolyTimeComputable fun z => List.replicate (parameter z) true
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · eval_unary_poly

```lean
theorem eval_unary_poly (p : PolyExpr) :
    PolyTimeComputable fun z => List.replicate (p.eval (parameter z)) true
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · description_poly

```lean
theorem description_poly (d : Data) : PolyTimeComputable (description d)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · description_shape

```lean
theorem description_shape (d : Data) (z : List Bool) :
    description d z = pairEncode (d.circuit (parameter z)).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (d.output (parameter z) j)))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · answers_poly

```lean
theorem answers_poly (d : Data) : PolyTimeComputable (answers d)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · message_poly

```lean
theorem message_poly (d : Data) : PolyTimeComputable (message d)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · message_layout

```lean
theorem message_layout (d : Data) (n : ℕ) (y f advice r : List Bool) :
    message d (NUPPT.layout (List.replicate n true) (pairEncode y f) advice r) =
      messageAt d n r f
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · view_poly

```lean
theorem view_poly (d : Data) :
    PolyTimeComputable (BobSimulator.raw (message d) (answers d))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · simulator

```lean
noncomputable def simulator (d : Data) (coins : PolyExpr) : NUPPT
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · simulator_eq

```lean
theorem simulator_eq (d : Data) (coins : PolyExpr) :
    simulator d coins = BobSimulator.simulator (message_poly d) (answers_poly d) coins
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · simulator_uniform

```lean
theorem simulator_uniform (d : Data) (coins : PolyExpr) : (simulator d coins).Uniform
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · simulator_coins

```lean
theorem simulator_coins (d : Data) (coins : PolyExpr) : (simulator d coins).coins = coins
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · answers_layout

```lean
theorem answers_layout (d : Data) (n : ℕ) (arg advice r : List Bool) :
    answers d (NUPPT.layout (List.replicate n true) arg advice r) = answersAt d n r
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · simulator_runAtL

```lean
theorem simulator_runAtL (d : Data) (coins : PolyExpr) (n : ℕ) (y f r : List Bool) :
    (simulator d coins).runAtL n (pairEncode y f) r =
      (⟨List.replicate n true, pairEncode y (answersAt d n r),
        [], [messageAt d n r f]⟩ : View).encode
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · simulator_runAt

```lean
theorem simulator_runAt (d : Data) (coins : PolyExpr) (n : ℕ) (y f : List Bool)
    (r : (simulator d coins).Coins n) :
    (simulator d coins).runAt n (pairEncode y f) r =
      (⟨List.replicate n true, pairEncode y (answersAt d n (List.ofFn r)),
        [], [messageAt d n (List.ofFn r) f]⟩ : View).encode
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · idealB_eq

```lean
theorem idealB_eq (d : Data) (coins : PolyExpr) (F : Functionality) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
    (r : (simulator d coins).Coins n) :
    F.idealB (simulator d coins) n x y r =
      pairEncode
        (⟨List.replicate n true, pairEncode (List.ofFn y) (answersAt d n (List.ofFn r)),
          [], [messageAt d n (List.ofFn r) (List.ofFn (F.f n x y).2)]⟩ : View).encode
        (List.ofFn (F.f n x y).1)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · messageAt_ofFn

```lean
theorem messageAt_ofFn (d : Data) (n : ℕ) (r : List Bool)
    (f : Fin (d.outLen.eval n) → Bool) :
    messageAt d n r (List.ofFn f) =
      FakeObjects.message (nestedSpecial d.E₁ d.E₂ n) (d.circuit n) (d.seed n r)
        (d.inA.eval n) (d.outLen.eval n) (d.output n) f
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · Data.make_messageAt

```lean
theorem Data.make_messageAt (n : ℕ) (r f : List Bool) :
    messageAt (Data.make
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation)) n r f =
      FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
        (inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulator.lean · Data.make_answersAt

```lean
theorem Data.make_answersAt (n : ℕ) (r : List Bool) :
    answersAt (Data.make
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation)) n r =
      List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n r)
        (inA.eval n) (inB.eval n))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FirstTagged.lean · polyTimeComputable_reencodeWords

```lean
theorem polyTimeComputable_reencodeWords :
    PolyTimeComputable fun w => BinArith.encWords (BinArith.decWords w)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FirstTagged.lean · firstTagged

```lean
noncomputable def firstTagged (F : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FirstTagged.lean · firstTagged_eq

```lean
theorem firstTagged_eq (F : List Bool → List Bool) (z : List Bool) :
    firstTagged F z =
      let rows
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FirstTagged.lean · firstTagged_poly

```lean
theorem firstTagged_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (firstTagged F)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FirstTagged.lean · firstTagged_encoded

```lean
theorem firstTagged_encoded {β : Type} (F : List Bool → List Bool) (q : List Bool)
    (rows : List (List Bool)) (f : List Bool → Option β) (payload : β → List Bool)
    (hspec : ∀ row, F (pairEncode q row) =
      match f row with | none => [] | some b => true :: payload b) :
    firstTagged F (pairEncode q (BinArith.encWords rows)) =
      match rows.findSome? f with
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarbledRun.lean · garbledStep

```lean
noncomputable def garbledStep (E₁ E₂ : List Bool → List Bool)
    (N tableWord : List Bool → List Bool) (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarbledRun.lean · garbledStep_eq

```lean
theorem garbledStep_eq (E₁ E₂ : List Bool → List Bool)
    (N tableWord : List Bool → List Bool) (w : List Bool) :
    garbledStep E₁ E₂ N tableWord w =
      evalGateAppendWord E₁ E₂ (pairEncode (N (pairFstD w))
        (pairEncode (pairSndD (pairFstD (pairSndD w)))
          (pairEncode (pairSndD (pairSndD w)) (tableWord w))))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarbledRun.lean · garbledStep_poly

```lean
theorem garbledStep_poly {E₁ E₂ N tableWord : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hN : PolyTimeComputable N) (hT : PolyTimeComputable tableWord) :
    PolyTimeComputable (garbledStep E₁ E₂ N tableWord)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarbledRun.lean · garbledRunWith_poly

```lean
theorem garbledRunWith_poly {E₁ E₂ N tableWord : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hN : PolyTimeComputable N) (gateCode : DAGGate → List Bool)
    (gs : List Bool → List DAGGate)
    (init : ∀ x, List (Fin (N x).length → Bool))
    (T : List Bool → ℕ → List (List Bool))
    (hgs : PolyTimeComputable fun x => BinArith.encWords ((gs x).map gateCode))
    (hinit : PolyTimeComputable fun x => BinArith.encWords ((init x).map List.ofFn))
    (hT : PolyTimeComputable tableWord)
    (hargs : ∀ g, pairSndD (gateCode g) =
      BinArith.encWords (g.args.map fun a => List.replicate a true))
    (htable : ∀ x g (vs : List (Fin (N x).length → Bool)),
      tableWord (pairEncode x
        (pairEncode (gateCode g) (BinArith.encWords (vs.map List.ofFn)))) =
          BinArith.encWords (T x vs.length)) :
    PolyTimeComputable fun x => BinArith.encWords
      ((runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ (N x).length) (T x) vs.length g vs)
        (gs x) (init x)).map List.ofFn)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · spEncStr_poly

```lean
theorem spEncStr_poly {E k m r : List Bool → List Bool} (hE : PolyTimeComputable E)
    (hk : PolyTimeComputable k) (hm : PolyTimeComputable m) (hr : PolyTimeComputable r) :
    PolyTimeComputable fun z => spEncStr E (k z) (m z) (r z)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · nestedWordEnc

```lean
def nestedWordEnc (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · nestedWordEnc_eq

```lean
theorem nestedWordEnc_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    nestedWordEnc E₁ E₂ z =
      if pairFstD z = [] then pairFstD (pairSndD z)
      else if pairSndD (pairFstD z) = [] then
        spEncStr E₁ (pairFstD (pairFstD z)) (pairFstD (pairSndD z))
          (pairFstD (pairSndD (pairSndD z)))
      else if pairSndD (pairSndD (pairFstD z)) = [] then
        spEncStr E₂ (pairFstD (pairFstD z))
          (spEncStr E₁ (pairFstD (pairSndD (pairFstD z))) (pairFstD (pairSndD z))
            (pairSndD (pairSndD (pairSndD z)))) (pairFstD (pairSndD (pairSndD z)))
      else []
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · nestedWordEnc_poly

```lean
theorem nestedWordEnc_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (nestedWordEnc E₁ E₂)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · nestedWordEnc_vectors

```lean
theorem nestedWordEnc_vectors {n : ℕ} (E₁ E₂ : List Bool → List Bool)
    (ks : List (Fin n → Bool)) (hks : ks.length ≤ 2) (o : Fin n → Bool)
    (r : (Fin n → Bool) × (Fin n → Bool)) :
    nestedWordEnc E₁ E₂
        (pairEncode (BinArith.encWords (ks.map List.ofFn))
          (pairEncode (List.ofFn o) (pairEncode (List.ofFn r.1) (List.ofFn r.2)))) =
      (nestedSpecial E₁ E₂ n).enc ks o r
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · garbledRow_poly

```lean
theorem garbledRow_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (inputs width : List Bool → ℕ) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : ∀ z, Fin (C z).gates.length)
    (a : ∀ z, Fin ((C z).gates[i z]).args.length → Bool)
    (hfan : ∀ z, ((C z).gates[i z]).args.length ≤ 2)
    (hkeys : PolyTimeComputable fun z =>
      BinArith.encWords ((argKeys (C z) (s z) (i z) (a z)).map List.ofFn))
    (hout : PolyTimeComputable fun z =>
      List.ofFn (keyAt (C z) (s z) (inputs z + i z)
        (gateOut ((C z).gates[i z]) (a z))))
    (hr₁ : PolyTimeComputable fun z => List.ofFn (((s z).2.1 (i z) (a z)).1))
    (hr₂ : PolyTimeComputable fun z => List.ofFn (((s z).2.1 (i z) (a z)).2)) :
    PolyTimeComputable fun z =>
      garbledRow (nestedSpecial E₁ E₂ (width z)) (C z) (s z) (i z) (a z)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · fixedTable_poly

```lean
theorem fixedTable_poly {α : Type} (enum : List α) (row : α → List Bool → List Bool)
    (hrow : ∀ a, PolyTimeComputable (row a)) :
    PolyTimeComputable fun z => BinArith.encWords (enum.map fun a => row a z)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · gateOut_small

```lean
theorem gateOut_small (g : DAGGate) (a : Fin g.args.length → Bool)
    (hfan : g.args.length ≤ 2) :
    gateOut g a =
      if g.kind = .and then
        if g.args.length = 0 then true else if g.args.length = 1 then
          (List.ofFn a).getD 0 false
        else (List.ofFn a).getD 0 false && (List.ofFn a).getD 1 false
      else if g.kind = .or then
        if g.args.length = 0 then false else if g.args.length = 1 then
          (List.ofFn a).getD 0 false
        else (List.ofFn a).getD 0 false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · gateOut_poly

```lean
theorem gateOut_poly (g : List Bool → DAGGate)
    (a : ∀ z, Fin (g z).args.length → Bool)
    (hfan : ∀ z, (g z).args.length ≤ 2)
    (hkAnd : PolyTimeComputable fun z => [decide ((g z).kind = .and)])
    (hkOr : PolyTimeComputable fun z => [decide ((g z).kind = .or)])
    (hzero : PolyTimeComputable fun z => [decide ((g z).args.length = 0)])
    (hone : PolyTimeComputable fun z => [decide ((g z).args.length = 1)])
    (h₀ : PolyTimeComputable fun z => [(List.ofFn (a z)).getD 0 false])
    (h₁ : PolyTimeComputable fun z => [(List.ofFn (a z)).getD 1 false]) :
    PolyTimeComputable fun z => [gateOut (g z) (a z)]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · gateKind_test_poly

```lean
theorem gateKind_test_poly (k : List Bool → GateKind)
    (hcode : PolyTimeComputable fun z => (k z).encode) (tag : GateKind) :
    PolyTimeComputable fun z => [decide (k z = tag)]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · keyList_small

```lean
private theorem keyList_small (args : List ℕ) (a : Fin args.length → Bool)
    (K : ℕ → Bool → List Bool) (hfan : args.length ≤ 2) :
    BinArith.encWords (List.ofFn fun t => K args[t] (a t)) =
      if args.length = 0 then []
      else if args.length = 1 then
        pairEncode (K (args.getD 0 0) ((List.ofFn a).getD 0 false)) []
      else
        pairEncode (K (args.getD 0 0) ((List.ofFn a).getD 0 false))
          (pairEncode (K (args.getD 1 0) ((List.ofFn a).getD 1 false)) [])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · argKeys_small

```lean
theorem argKeys_small {m n : ℕ} (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (hfan : (C.gates[i]).args.length ≤ 2) :
    BinArith.encWords ((argKeys C s i a).map List.ofFn) =
      if (C.gates[i]).args.length = 0 then []
      else if (C.gates[i]).args.length = 1 then
        pairEncode (List.ofFn (keyAt C s ((C.gates[i]).args.getD 0 0)
          ((List.ofFn a).getD 0 false))) []
      else
        pairEncode (List.ofFn (keyAt C s ((C.gates[i]).args.getD 0 0)
          ((List.ofFn a).getD 0 false)))
          (pairEncode (List.ofFn (keyAt C s ((C.gates[i]).args.getD 1 0)
            ((List.ofFn a).getD 1 false))) [])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · argKeys_poly

```lean
theorem argKeys_poly (inputs width : List Bool → ℕ) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : ∀ z, Fin (C z).gates.length)
    (a : ∀ z, Fin ((C z).gates[i z]).args.length → Bool)
    (hfan : ∀ z, ((C z).gates[i z]).args.length ≤ 2)
    (hzero : PolyTimeComputable fun z => [decide (((C z).gates[i z]).args.length = 0)])
    (hone : PolyTimeComputable fun z => [decide (((C z).gates[i z]).args.length = 1)])
    (h₀ : PolyTimeComputable fun z =>
      List.ofFn (keyAt (C z) (s z) (((C z).gates[i z]).args.getD 0 0)
        ((List.ofFn (a z)).getD 0 false)))
    (h₁ : PolyTimeComputable fun z =>
      List.ofFn (keyAt (C z) (s z) (((C z).gates[i z]).args.getD 1 0)
        ((List.ofFn (a z)).getD 1 false))) :
    PolyTimeComputable fun z =>
      BinArith.encWords ((argKeys (C z) (s z) (i z) (a z)).map List.ofFn)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean · smallArityTable_poly

```lean
theorem smallArityTable_poly (arity : List Bool → ℕ)
    (enum : ∀ l : ℕ, List (Fin l → Bool))
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool)
    (hbound : ∀ z, arity z ≤ 2)
    (hzero : PolyTimeComputable fun z => [decide (arity z = 0)])
    (hone : PolyTimeComputable fun z => [decide (arity z = 1)])
    (hrow : ∀ l, l ≤ 2 → ∀ a, PolyTimeComputable (row l a)) :
    PolyTimeComputable fun z =>
      BinArith.encWords ((enum (arity z)).map fun a => row (arity z) a z)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean · gatesWord

```lean
def gatesWord (description : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean · gatesWord_eq

```lean
theorem gatesWord_eq (description : List Bool → List Bool) (z : List Bool) :
    gatesWord description z =
      pairSndD (DescriptionDecoder.readCircuit (pairFstD (description z)))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean · gatesWord_poly

```lean
theorem gatesWord_poly {description : List Bool → List Bool}
    (hdescription : PolyTimeComputable description) : PolyTimeComputable (gatesWord description)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean · gatesWord_description

```lean
theorem gatesWord_description (description : List Bool → List Bool) (z : List Bool)
    {m : ℕ} (C : DAGCircuit m) (outs : List Bool)
    (hdescription : description z = pairEncode C.encode outs) :
    gatesWord description z = BinArith.encWords (C.gates.map DescriptionDecoder.gateRecord)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean · tables_poly

```lean
theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs : List Bool → ℕ)
    (description outs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hshape : ∀ z, description z = pairEncode (C z).encode (outs z))
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i =>
      BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · message

```lean
noncomputable def message (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · message_eq

```lean
theorem message_eq (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ) :
    message M C s inA outLen output v stage =
      pairEncode (BinArith.encWords (List.ofFn fun i =>
          BinArith.encWords (GateHybrids.tableWith M C s
            (GateHybrids.stageBit C v stage) i)))
        (pairEncode
          (BinArith.encWords (List.ofFn fun w : Fin inA => List.ofFn (keyAt C s w false)))
          (BinArith.encWords (List.ofFn fun j =>
            pairEncode (List.ofFn (FakeObjects.decodePair C s (output j) (v (output j))).1)
              (List.ofFn (FakeObjects.decodePair C s (output j) (v (output j))).2))))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · sample

```lean
noncomputable def sample (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) (stage : ℕ) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · sample_eq

```lean
theorem sample_eq (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) (stage : ℕ) :
    sample M C s inA inB outLen output v commonInput bobInput bobCoins aliceOutput stage =
      pairEncode (⟨commonInput,
        pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB)),
        bobCoins, [message M C s inA outLen output v stage]⟩ : View).encode aliceOutput
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · activeAnswers_relabel

```lean
theorem activeAnswers_relabel (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (v : ℕ → Bool) (first count : ℕ) :
    FakeObjects.activeAnswers C (RelabelGarbling.relabelSeed C v s) first count =
      fun t => keyAt C s (first + t.divNat) (v (first + t.divNat)) t.modNat
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · decodePair_relabel

```lean
theorem decodePair_relabel (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (v : ℕ → Bool) (w : ℕ) :
    FakeObjects.decodePair C (RelabelGarbling.relabelSeed C v s) w (v w) =
      (keyAt C s w false, keyAt C s w true)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · message_relabel

```lean
theorem message_relabel (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) :
    pairEncode (BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (garbledTable M C s i)))
      (pairEncode
        (BinArith.encWords (List.ofFn fun w : Fin inA =>
          List.ofFn (keyAt C s w (v w))))
        (BinArith.encWords (List.ofFn fun j =>
          pairEncode (List.ofFn (keyAt C s (output j) false))
            (List.ofFn (keyAt C s (output j) true))))) =
      message M C (RelabelGarbling.relabelSeed C v s) inA outLen output v 0
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · message_end

```lean
theorem message_end (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) :
    message M C s inA outLen output v (2 * C.gates.length) =
      FakeObjects.message M C s inA outLen output (fun j => v (output j))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · sample_relabel

```lean
theorem sample_relabel (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) :
    pairEncode (⟨commonInput,
      pairEncode bobInput (List.ofFn fun t : Fin (inB * width) =>
        keyAt C s (inA + t.divNat) (v (inA + t.divNat)) t.modNat), bobCoins,
      [pairEncode (BinArith.encWords (List.ofFn fun i =>
          BinArith.encWords (garbledTable M C s i)))
        (pairEncode
          (BinArith.encWords (List.ofFn fun w : Fin inA =>
            List.ofFn (keyAt C s w (v w))))
          (BinArith.encWords (List.ofFn fun j =>
            pairEncode (List.ofFn (keyAt C s (output j) false))
              (List.ofFn (keyAt C s (output j) true)))))]⟩ : View).encode aliceOutput =
      sample M C (RelabelGarbling.relabelSeed C v s) inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput 0
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean · sample_end

```lean
theorem sample_end (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) :
    sample M C s inA inB outLen output v commonInput bobInput bobCoins aliceOutput
        (2 * C.gates.length) =
      pairEncode (⟨commonInput,
        pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB)),
        bobCoins, [FakeObjects.message M C s inA outLen output
          (fun j => v (output j))]⟩ : View).encode aliceOutput
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · rowWith

```lean
def rowWith (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs) (s : GarbleSeed C K ρ)
    (bit : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) : Cipher
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · rowWith_eq

```lean
theorem rowWith_eq (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ)
    (bit : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    rowWith M C s bit i a =
      M.enc (argKeys C s i a) (keyAt C s (inputs + i) (bit i a)) (s.2.1 i a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · tableWith

```lean
noncomputable def tableWith (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ)
    (bit : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) : List Cipher
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · tableWith_eq

```lean
theorem tableWith_eq (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ)
    (bit : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) :
    tableWith M C s bit i =
      (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map
        fun a => rowWith M C s bit i (s.2.2 i a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · tableWith_congr

```lean
theorem tableWith_congr (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ)
    (bit bit' : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) (h : ∀ a, bit i a = bit' i a) :
    tableWith M C s bit i = tableWith M C s bit' i
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · rowWith_real

```lean
theorem rowWith_real (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    rowWith M C s (fun j b => gateOut (C.gates[j]) b) i a = garbledRow M C s i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · rowWith_fake

```lean
theorem rowWith_fake (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    rowWith M C s (fun _ _ => false) i a = FakeObjects.row M C s i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · tableWith_real

```lean
theorem tableWith_real (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    tableWith M C s (fun j b => gateOut (C.gates[j]) b) i = garbledTable M C s i
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · tableWith_fake

```lean
theorem tableWith_fake (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    tableWith M C s (fun _ _ => false) i = FakeObjects.table M C s i
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · trueBit

```lean
def trueBit (C : DAGCircuit inputs) (v : ℕ → Bool) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · trueBit_eq

```lean
theorem trueBit_eq (C : DAGCircuit inputs) (v : ℕ → Bool) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    trueBit C v i a =
      xor (gateOut (C.gates[i]) (xorPerm (RelabelGarbling.argValues C v i) a))
        (v (inputs + i))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · trueBit_zero

```lean
theorem trueBit_zero (C : DAGCircuit inputs) (v : ℕ → Bool)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (inputs + i))
    (i : Fin C.gates.length) : trueBit C v i (fun _ => false) = false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · values_consistent

```lean
theorem values_consistent (C : DAGCircuit inputs) (x : Fin inputs → Bool)
    (i : Fin C.gates.length) :
    gateOut (C.gates[i])
        (RelabelGarbling.argValues C (fun w => (C.values x).getD w false) i) =
      (C.values x).getD (inputs + i) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · tableWith_relabel

```lean
theorem tableWith_relabel (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (v : ℕ → Bool) (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    garbledTable M C s i =
      tableWith M C (RelabelGarbling.relabelSeed C v s) (trueBit C v) i
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit

```lean
def outputBit (C : DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_eq

```lean
theorem outputBit_eq (C : DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    outputBit C v cutoff phase i a =
      if (i : ℕ) < cutoff ∨ ((i : ℕ) = cutoff ∧ phase ≠ 0 ∧
        (List.ofFn a).getD 0 false = true) then false else trueBit C v i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · stageBit

```lean
def stageBit (C : DAGCircuit inputs) (v : ℕ → Bool) (t : ℕ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · stageBit_eq

```lean
theorem stageBit_eq (C : DAGCircuit inputs) (v : ℕ → Bool) (t : ℕ) :
    stageBit C v t = outputBit C v (t / 2) (t % 2)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_start

```lean
theorem outputBit_start (C : DAGCircuit inputs) (v : ℕ → Bool) :
    outputBit C v 0 0 = trueBit C v
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_end

```lean
theorem outputBit_end (C : DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ)
    (hc : C.gates.length ≤ cutoff) :
    outputBit C v cutoff phase = fun _ _ => false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · stageBit_even

```lean
theorem stageBit_even (C : DAGCircuit inputs) (v : ℕ → Bool) (k : ℕ) :
    stageBit C v (2 * k) = outputBit C v k 0
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · stageBit_odd

```lean
theorem stageBit_odd (C : DAGCircuit inputs) (v : ℕ → Bool) (k : ℕ) :
    stageBit C v (2 * k + 1) = outputBit C v k 1
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · tableWith_end

```lean
theorem tableWith_end (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (v : ℕ → Bool) (i : Fin C.gates.length) :
    tableWith M C s (stageBit C v (2 * C.gates.length)) i =
      FakeObjects.table M C s i
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_completed

```lean
theorem outputBit_completed (C : DAGCircuit inputs) (v : ℕ → Bool)
    (cutoff phase : ℕ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) (hi : (i : ℕ) < cutoff) :
    outputBit C v cutoff phase i a = false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_future

```lean
theorem outputBit_future (C : DAGCircuit inputs) (v : ℕ → Bool)
    (cutoff phase : ℕ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) (hi : cutoff < (i : ℕ)) :
    outputBit C v cutoff phase i a = trueBit C v i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_current_zero

```lean
theorem outputBit_current_zero (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    outputBit C v i 0 i a = trueBit C v i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_current_first

```lean
theorem outputBit_current_first (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (ha : (List.ofFn a).getD 0 false = true) :
    outputBit C v i 1 i a = false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_current_rest

```lean
theorem outputBit_current_rest (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (ha : (List.ofFn a).getD 0 false = false) :
    outputBit C v i 1 i a = trueBit C v i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_zero

```lean
theorem outputBit_zero (C : DAGCircuit inputs) (v : ℕ → Bool)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (inputs + i))
    (cutoff phase : ℕ) (i : Fin C.gates.length) :
    outputBit C v cutoff phase i (fun _ => false) = false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · assignment_zero_of_two

```lean
theorem assignment_zero_of_two {l : ℕ} (hl : l ≤ 2) (a : Fin l → Bool)
    (h₀ : (List.ofFn a).getD 0 false = false)
    (h₁ : (List.ofFn a).getD 1 false = false) : a = fun _ => false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_first_unchanged

```lean
theorem outputBit_first_unchanged (C : DAGCircuit inputs) (v : ℕ → Bool)
    (cutoff : ℕ) (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (h : (i : ℕ) ≠ cutoff ∨ (List.ofFn a).getD 0 false = false) :
    outputBit C v cutoff 0 i a = outputBit C v cutoff 1 i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_second_other

```lean
theorem outputBit_second_other (C : DAGCircuit inputs) (v : ℕ → Bool)
    (cutoff : ℕ) (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (hi : (i : ℕ) ≠ cutoff) :
    outputBit C v cutoff 1 i a = outputBit C v (cutoff + 1) 0 i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · outputBit_second_unchanged

```lean
theorem outputBit_second_unchanged (C : DAGCircuit inputs) (v : ℕ → Bool)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (inputs + i))
    (cutoff : ℕ) (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (h : (i : ℕ) ≠ cutoff ∨ (List.ofFn a).getD 0 false = true ∨
      (List.ofFn a).getD 1 false = false) :
    outputBit C v cutoff 1 i a = outputBit C v (cutoff + 1) 0 i a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · stageBit_start

```lean
theorem stageBit_start (C : DAGCircuit inputs) (v : ℕ → Bool) :
    stageBit C v 0 = trueBit C v
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean · tableWith_start

```lean
theorem tableWith_start (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (v : ℕ → Bool) (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    garbledTable M C s i =
      tableWith M C (RelabelGarbling.relabelSeed C v s) (stageBit C v 0) i
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · selectedPosition

```lean
def selectedPosition (g : DAGGate) (a : Fin g.args.length → Bool) (u : ℕ) :
    Option (Fin g.args.length)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · selectedPosition_eq

```lean
theorem selectedPosition_eq (g : DAGGate) (a : Fin g.args.length → Bool) (u : ℕ) :
    selectedPosition g a u =
      (List.finRange g.args.length).find? fun p => decide (g.args[p.val] = u ∧ a p = true)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · selectedPosition_eq_some_iff

```lean
theorem selectedPosition_eq_some_iff (g : DAGGate) (a : Fin g.args.length → Bool) (u : ℕ)
    (hargs : g.args.Nodup) (p : Fin g.args.length) :
    selectedPosition g a u = some p ↔ g.args[p.val] = u ∧ a p = true
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · rowSlots

```lean
def rowSlots (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ) : List (ℕ × ℕ)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · rowSlots_eq

```lean
theorem rowSlots_eq (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ) :
    rowSlots g rows perm u = (List.range rows.length).filterMap (fun r =>
      (selectedPosition g (perm (rows.getD r (fun _ => false))) u).map fun p => (r, p.val))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · occurrences

```lean
def occurrences {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) : List (Fin C.gates.length × ℕ × ℕ)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · occurrences_eq

```lean
theorem occurrences_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) :
    occurrences C rows perm u = (List.finRange C.gates.length).flatMap (fun i =>
      (rowSlots C.gates[i.val] (rows i) (perm i) u).map fun rp => (i, rp))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · mem_rowSlots_iff

```lean
theorem mem_rowSlots_iff (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u r p : ℕ) (hargs : g.args.Nodup) :
    (r, p) ∈ rowSlots g rows perm u ↔ r < rows.length ∧
      ∃ hp : p < g.args.length, g.args[p] = u ∧
        perm (rows.getD r (fun _ => false)) ⟨p, hp⟩ = true
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · mem_occurrences_iff

```lean
theorem mem_occurrences_iff {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (r p : ℕ) (hargs : C.gates[i.val].args.Nodup) :
    (i, r, p) ∈ occurrences C rows perm u ↔ r < (rows i).length ∧
      ∃ hp : p < C.gates[i.val].args.length, C.gates[i.val].args[p] = u ∧
        perm i ((rows i).getD r (fun _ => false)) ⟨p, hp⟩ = true
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · exhaustive

```lean
theorem exhaustive {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (hargs : C.gates[i.val].args.Nodup)
    (hcomplete : ∀ a, a ∈ rows i) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length) (hvertex : C.gates[i.val].args[p.val] = u)
    (hbit : a p = true) :
    ∃ r, (i, r, p.val) ∈ occurrences C rows perm u ∧
      perm i ((rows i).getD r (fun _ => false)) = a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · per_row_unique

```lean
theorem per_row_unique {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (r p p' : ℕ) (hargs : C.gates[i.val].args.Nodup)
    (h : (i, r, p) ∈ occurrences C rows perm u)
    (h' : (i, r, p') ∈ occurrences C rows perm u) : p = p'
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · rowSlots_nodup

```lean
theorem rowSlots_nodup (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ) :
    (rowSlots g rows perm u).Nodup
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · occurrences_nodup

```lean
theorem occurrences_nodup {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) : (occurrences C rows perm u).Nodup
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · length_rowSlots_le_four

```lean
theorem length_rowSlots_le_four (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ)
    (hrows : rows.Nodup) (hfanin : g.args.length ≤ 2) :
    (rowSlots g rows perm u).length ≤ 4
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · length_occurrences_le

```lean
theorem length_occurrences_le {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (hrows : ∀ i, (rows i).Nodup) (hfanin : C.IsFaninTwo) :
    (occurrences C rows perm u).length ≤ 4 * C.gates.length
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · padded

```lean
def padded {α : Type*} (q : ℕ) (slots : List α) : Fin (q + 1) → Option α
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · padded_eq

```lean
theorem padded_eq {α : Type*} (q : ℕ) (slots : List α) (j : Fin (q + 1)) :
    padded q slots j = slots[j.val]?
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · padded_some_iff

```lean
theorem padded_some_iff {α : Type*} (q : ℕ) (slots : List α)
    (hlen : slots.length ≤ q + 1) (a : α) :
    (∃ j, padded q slots j = some a) ↔ a ∈ slots
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · padded_eq_none_iff

```lean
theorem padded_eq_none_iff {α : Type*} (q : ℕ) (slots : List α) (j : Fin (q + 1)) :
    padded q slots j = none ↔ slots.length ≤ j.val
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · padded_occurrences_some_iff

```lean
theorem padded_occurrences_some_iff {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (hrows : ∀ i, (rows i).Nodup) (hfanin : C.IsFaninTwo)
    (hbudget : 4 * C.gates.length ≤ q + 1) (s : Fin C.gates.length × ℕ × ℕ) :
    (∃ j, padded q (occurrences C rows perm u) j = some s) ↔
      s ∈ occurrences C rows perm u
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · selected_wire_lt

```lean
theorem selected_wire_lt {m : ℕ} (C : DAGCircuit m) (i₀ : Fin C.gates.length)
    (u : ℕ) (hu : u ∈ C.gates[i₀.val].args) : u < m + i₀.val
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · hybrid_plaintext_ne

```lean
theorem hybrid_plaintext_ne (m i₀ u j : ℕ) (hu : u < m + i₀) (b : Bool) :
    (m + j, if j < i₀ then false else b) ≠ (u, true)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · hybrid_plaintext_ne_of_used

```lean
theorem hybrid_plaintext_ne_of_used {m : ℕ} (C : DAGCircuit m)
    (i₀ : Fin C.gates.length) (u : ℕ) (hu : u ∈ C.gates[i₀.val].args) (j : ℕ) (b : Bool) :
    (m + j, if j < i₀.val then false else b) ≠ (u, true)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · active_label_ne

```lean
theorem active_label_ne (v u : ℕ) : (v, false) ≠ (u, true)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean · decoding_label_ne

```lean
theorem decoding_label_ne {m k : ℕ} (C : DAGCircuit m) (i₀ : Fin C.gates.length)
    (u : ℕ) (hu : u ∈ C.gates[i₀.val].args) (outs : Fin k → ℕ)
    (hsink : ∀ j g, g ∈ C.gates → outs j ∉ g.args) (j : Fin k) (b : Bool) :
    (outs j, b) ≠ (u, true)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_spEncStr_le

```lean
theorem length_spEncStr_le (E : List Bool → List Bool) (k m r : List Bool) :
    (spEncStr E k m r).length ≤ 3 * r.length + m.length + 2
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_nestedSpecial_enc_le

```lean
theorem length_nestedSpecial_enc_le (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    (ks : List (Fin n → Bool)) (o : Fin n → Bool)
    (r : (Fin n → Bool) × (Fin n → Bool)) :
    ((nestedSpecial E₁ E₂ n).enc ks o r).length ≤ 7 * n + 4
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · encodeMsgs_eq_encWords

```lean
theorem encodeMsgs_eq_encWords (L : List (List Bool)) :
    Strategy.encodeMsgs L = BinArith.encWords L
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_garbledRow_le

```lean
theorem length_garbledRow_le (E₁ E₂ : List Bool → List Bool) (n : ℕ) {m : ℕ}
    (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    (garbledRow (nestedSpecial E₁ E₂ n) C s i a).length ≤ 7 * n + 4
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_garbledTable_le

```lean
theorem length_garbledTable_le {K W ρ : Type} [Inhabited K] {m : ℕ}
    (M : MultiEnc K W ρ) (C : DAGCircuit m) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) (hi : (C.gates[i]).args.length ≤ 2) :
    (garbledTable M C s i).length ≤ 4
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_encoded_garbledTable_le

```lean
theorem length_encoded_garbledTable_le (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    {m : ℕ} (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (i : Fin C.gates.length) (hi : (C.gates[i]).args.length ≤ 2) :
    (Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) C s i)).length ≤
      56 * n + 40
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_encoded_garbledTables_le

```lean
theorem length_encoded_garbledTables_le (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    {m : ℕ} (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (hC : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) :
    (Strategy.encodeMsgs (List.ofFn fun i : Fin C.gates.length =>
      Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) C s i))).length ≤
      C.gates.length * (112 * n + 82)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_encoded_keys_le

```lean
theorem length_encoded_keys_le {a n : ℕ} (keys : Fin a → Fin n → Bool) :
    (Strategy.encodeMsgs (List.ofFn fun i => List.ofFn (keys i))).length ≤
      a * (2 * n + 2)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_encoded_pairs_le

```lean
theorem length_encoded_pairs_le {o n : ℕ} (keys : Fin o → Bool → Fin n → Bool) :
    (Strategy.encodeMsgs (List.ofFn fun j =>
      pairEncode (List.ofFn (keys j false)) (List.ofFn (keys j true)))).length ≤
      o * (6 * n + 6)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean · length_message_of_parts_le

```lean
theorem length_message_of_parts_le (tables keys pairs : List Bool) (g a o n : ℕ)
    (ht : tables.length ≤ g * (112 * n + 82))
    (hk : keys.length ≤ a * (2 * n + 2))
    (hp : pairs.length ≤ o * (6 * n + 6)) :
    (pairEncode tables (pairEncode keys pairs)).length ≤
      2 * (g * (112 * n + 82)) + 2 * (a * (2 * n + 2)) + o * (6 * n + 6) + 4
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTAnswerWords.lean · length_answersB

```lean
theorem length_answersB (H : HybridProtocol otFunctionality) (n : ℕ)
    (xs ys rA rB : List Bool) :
    (H.answersB n xs ys rA rB).length = H.calls.eval n
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTAnswerWords.lean · answersB_eq_active

```lean
theorem answersB_eq_active {m width : ℕ} {ρ : Type}
    (H : HybridProtocol otFunctionality) (n : ℕ) (xs ys rA rB : List Bool)
    (C : DAGCircuit m) (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ)
    (v : ℕ → Bool) (hCalls : H.calls.eval n = count * width)
    (hv : ∀ i : Fin count, v (first + i) = ys.getD i false)
    (hpoint : ∀ (i : Fin count) (t : Fin width),
      (H.answersB n xs ys rA rB).getD (i * width + t) false =
        keyAt C s (first + i) (ys.getD i false) t) :
    H.answersB n xs ys rA rB =
      List.ofFn (FakeObjects.activeAnswers C (RelabelGarbling.relabelSeed C v s) first count)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTAnswerWords.lean · answersA_nil

```lean
theorem answersA_nil (H : HybridProtocol otFunctionality) (n : ℕ)
    (xs ys rA rB : List Bool) : H.answersA n xs ys rA rB = []
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTInputs.lean · otInputA

```lean
def otInputA (inA sizeBound : PolyExpr) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTInputs.lean · otInputA_eq

```lean
theorem otInputA_eq (inA sizeBound : PolyExpr) (z : List Bool) :
    otInputA inA sizeBound z =
      [(pairFstD (pairSndD (pairSndD z))).getD
          (inA.eval (pairFstD z).length * (pairFstD z).length +
            (pairSndD (pairSndD (pairSndD z))).length) false,
        (pairFstD (pairSndD (pairSndD z))).getD
          ((sizeBound.eval (pairFstD z).length + inA.eval (pairFstD z).length) *
            (pairFstD z).length + (pairSndD (pairSndD (pairSndD z))).length) false]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTInputs.lean · otInputA_layout

```lean
theorem otInputA_layout (inA sizeBound : PolyExpr) (n j : ℕ) (x r : List Bool) :
    otInputA inA sizeBound (pairEncode (List.replicate n true)
      (pairEncode x (pairEncode r (List.replicate j true)))) =
      [r.getD (inA.eval n * n + j) false,
        r.getD ((sizeBound.eval n + inA.eval n) * n + j) false]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTInputs.lean · polyTimeComputable_otInputA

```lean
theorem polyTimeComputable_otInputA (inA sizeBound : PolyExpr) :
    PolyTimeComputable (otInputA inA sizeBound)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTInputs.lean · otInputB

```lean
def otInputB (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTInputs.lean · otInputB_eq

```lean
theorem otInputB_eq (z : List Bool) :
    otInputB z = [(pairFstD (pairSndD z)).getD
      ((pairSndD (pairSndD (pairSndD z))).length / (pairFstD z).length) false]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTInputs.lean · otInputB_layout

```lean
theorem otInputB_layout (n j : ℕ) (y r : List Bool) :
    otInputB (pairEncode (List.replicate n true)
      (pairEncode y (pairEncode r (List.replicate j true)))) =
      [y.getD (j / n) false]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/OTInputs.lean · polyTimeComputable_otInputB

```lean
theorem polyTimeComputable_otInputB : PolyTimeComputable otInputB
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ProtocolEfficiency.lean · aliceMessageBound

```lean
def aliceMessageBound (S A O : PolyExpr) : PolyExpr
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ProtocolEfficiency.lean · aliceMessageBound_eq

```lean
theorem aliceMessageBound_eq (S A O : PolyExpr) (n : ℕ) :
    (aliceMessageBound S A O).eval n =
      2 * (S.eval n * (112 * n + 82)) + 2 * (A.eval n * (2 * n + 2)) +
        O.eval n * (6 * n + 6) + 4
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ProtocolEfficiency.lean · twoMove_message_length_le

```lean
theorem twoMove_message_length_le (π : Protocol)
    (msgA : List Bool → List Bool → List Bool → List Bool)
    (msgB : List Bool → List Bool → List Bool → List Bool → List Bool)
    (hR : π.rounds = .const 2) (hF : π.verifierFirst = false)
    (hA : ∀ w z r, π.P.next w z r [] = msgA w z r)
    (hB : ∀ w z r a, π.V.next w z r [a] = msgB w z r a)
    (BA BB : PolyExpr)
    (hLA : ∀ w z r, (msgA w z r).length ≤ BA.eval w.length)
    (hLB : ∀ w z r a, (msgB w z r a).length ≤ BB.eval w.length)
    (w zA zB : List Bool) (r : π.ExecCoins π.P w) (msg : List Bool)
    (hmsg : msg ∈ (π.transcript w zA zB r).1 ++ (π.transcript w zA zB r).2) :
    msg.length ≤ (PolyExpr.add BA BB).eval w.length
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · argValues

```lean
def argValues {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) (i : Fin C.gates.length) :
    Fin (C.gates[i]).args.length → Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · argValues_eq

```lean
theorem argValues_eq {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    (i : Fin C.gates.length) :
    argValues C v i = fun t => v ((C.gates[i]).args[t])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · argValues_apply

```lean
theorem argValues_apply {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    (i : Fin C.gates.length) (t : Fin (C.gates[i]).args.length) :
    argValues C v i t = v ((C.gates[i]).args[t])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · relabelSeed

```lean
def relabelSeed {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) : GarbleSeed C K ρ
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · relabelSeed_eq

```lean
theorem relabelSeed_eq {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) :
    relabelSeed C v s =
      ((fun w b => s.1 w (xor b (v w))),
        (fun i a => s.2.1 i (xorPerm (argValues C v i) a)),
        fun i => (s.2.2 i).trans (xorPerm (argValues C v i)))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · relabelSeed_key

```lean
theorem relabelSeed_key {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) (w : Fin C.size) (b : Bool) :
    (relabelSeed C v s).1 w b = s.1 w (xor b (v w))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · relabelSeed_coin

```lean
theorem relabelSeed_coin {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    (relabelSeed C v s).2.1 i a = s.2.1 i (xorPerm (argValues C v i) a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · relabelSeed_perm

```lean
theorem relabelSeed_perm {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    (relabelSeed C v s).2.2 i a = xorPerm (argValues C v i) (s.2.2 i a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · keyAt_relabel

```lean
theorem keyAt_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (w : ℕ) (b : Bool) :
    keyAt C (relabelSeed C v s) w b = keyAt C s w (xor b (v w))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · keyAt_original

```lean
theorem keyAt_original {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (w : ℕ) (b : Bool) :
    keyAt C s w b = keyAt C (relabelSeed C v s) w (xor b (v w))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · argKeys_relabel

```lean
theorem argKeys_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    argKeys C (relabelSeed C v s) i a =
      argKeys C s i (xorPerm (argValues C v i) a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · row_relabel

```lean
theorem row_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K W ρ : Type} [Inhabited K] (M : MultiEnc K W ρ) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    M.enc (argKeys C (relabelSeed C v s) i a)
        (keyAt C (relabelSeed C v s) (m + i)
          (xor (gateOut (C.gates[i]) (xorPerm (argValues C v i) a)) (v (m + i))))
        ((relabelSeed C v s).2.1 i a) =
      garbledRow M C s i (xorPerm (argValues C v i) a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · garbledTable_relabel

```lean
theorem garbledTable_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K W ρ : Type} [Inhabited K] (M : MultiEnc K W ρ) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) :
    garbledTable M C s i =
      (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map
        (fun a =>
          let b := (relabelSeed C v s).2.2 i a
          M.enc (argKeys C (relabelSeed C v s) i b)
            (keyAt C (relabelSeed C v s) (m + i)
              (xor (gateOut (C.gates[i]) (xorPerm (argValues C v i) b)) (v (m + i))))
            ((relabelSeed C v s).2.1 i b))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · inputKeys_relabel

```lean
theorem inputKeys_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (x : Fin m → Bool) :
    inputKeys C (relabelSeed C v s) x = inputKeys C s (fun i => xor (x i) (v i))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · selectedKeys_original

```lean
theorem selectedKeys_original {m k : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (wire : Fin k → ℕ)
    (bits : Fin k → Bool) :
    (List.ofFn fun j => keyAt C s (wire j) (bits j)) =
      (List.ofFn fun j => keyAt C (relabelSeed C v s) (wire j)
        (xor (bits j) (v (wire j))))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RelabelGarbling.lean · output_pair_relabel

```lean
theorem output_pair_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (w : ℕ) :
    (keyAt C s w false, keyAt C s w true) =
      if v w then
        (keyAt C (relabelSeed C v s) w true, keyAt C (relabelSeed C v s) w false)
      else (keyAt C (relabelSeed C v s) w false, keyAt C (relabelSeed C v s) w true)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · assignmentBit

```lean
def assignmentBit (width bound gate : List Bool → ℕ) (coins : List Bool → List Bool)
    (l : ℕ) (a : Fin l → Bool) (j : ℕ) (z : List Bool) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · assignmentBit_eq

```lean
theorem assignmentBit_eq (width bound gate : List Bool → ℕ) (coins : List Bool → List Bool)
    (l : ℕ) (a : Fin l → Bool) (j : ℕ) (z : List Bool) :
    assignmentBit width bound gate coins l a j z =
      if j < l then xor ((List.ofFn a).getD j false)
        ((coins z).getD (10 * bound z * width z + 2 * gate z + j) false) else false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · assignmentBit_poly

```lean
theorem assignmentBit_poly {width bound gate : List Bool → ℕ} {coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hcoins : PolyTimeComputable coins) (l : ℕ) (a : Fin l → Bool) (j : ℕ) :
    PolyTimeComputable fun z => [assignmentBit width bound gate coins l a j z]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · gateBit

```lean
def gateBit (kind : List Bool → List Bool) (l : ℕ) (b₀ b₁ : List Bool → Bool)
    (z : List Bool) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · gateBit_eq

```lean
theorem gateBit_eq (kind : List Bool → List Bool) (l : ℕ) (b₀ b₁ : List Bool → Bool)
    (z : List Bool) :
    gateBit kind l b₀ b₁ z =
      if kind z = [false, false] then
        if l = 0 then true else if l = 1 then b₀ z else b₀ z && b₁ z
      else if kind z = [false, true] then
        if l = 0 then false else if l = 1 then b₀ z else b₀ z
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · gateBit_poly

```lean
theorem gateBit_poly {kind : List Bool → List Bool} (hkind : PolyTimeComputable kind)
    (l : ℕ) {b₀ b₁ : List Bool → Bool}
    (h₀ : PolyTimeComputable fun z => [b₀ z])
    (h₁ : PolyTimeComputable fun z => [b₁ z]) :
    PolyTimeComputable fun z => [gateBit kind l b₀ b₁ z]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · keyWord

```lean
def keyWord (width bound vertex : List Bool → ℕ) (bit : List Bool → Bool)
    (coins : List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · keyWord_eq

```lean
theorem keyWord_eq (width bound vertex : List Bool → ℕ) (bit : List Bool → Bool)
    (coins : List Bool → List Bool) (z : List Bool) :
    keyWord width bound vertex bit coins z =
      List.ofFn fun t : Fin (width z) =>
        (coins z).getD (((bit z).toNat * bound z + vertex z) * width z + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · keyWord_poly

```lean
theorem keyWord_poly {width bound vertex : List Bool → ℕ} {bit : List Bool → Bool}
    {coins : List Bool → List Bool} (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hvertex : PolyTimeComputable fun z => List.replicate (vertex z) true)
    (hbit : PolyTimeComputable fun z => [bit z]) :
    PolyTimeComputable (keyWord width bound vertex bit coins)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · nonceWord

```lean
def nonceWord (width bound gate index : List Bool → ℕ) (coins : List Bool → List Bool)
    (half : Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · nonceWord_eq

```lean
theorem nonceWord_eq (width bound gate index : List Bool → ℕ) (coins : List Bool → List Bool)
    (half : Bool) (z : List Bool) :
    nonceWord width bound gate index coins half z =
      List.ofFn fun t : Fin (width z) =>
        (coins z).getD (2 * bound z * width z + (4 * gate z + index z) * (2 * width z) +
          half.toNat * width z + t) false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · nonceWord_poly

```lean
theorem nonceWord_poly {width bound gate index : List Bool → ℕ}
    {coins : List Bool → List Bool} (half : Bool) (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hindex : PolyTimeComputable fun z => List.replicate (index z) true) :
    PolyTimeComputable (nonceWord width bound gate index coins half)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWordWith

```lean
def rowWordWith (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (args coins : List Bool → List Bool) (outputBit : List Bool → Bool) (l : ℕ) (a : Fin l → Bool)
    (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWordWith_eq

```lean
theorem rowWordWith_eq (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (args coins : List Bool → List Bool) (outputBit : List Bool → Bool)
    (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWordWith E₁ E₂ width bound inputs gate args coins outputBit l a z =
      let b₀
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWord

```lean
def rowWord (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (kind args coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool)
    (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWord_eq

```lean
theorem rowWord_eq (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (kind args coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWord E₁ E₂ width bound inputs gate kind args coins l a z =
      let b₀
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWordWith_poly

```lean
theorem rowWordWith_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs gate : List Bool → ℕ}
    {args coins : List Bool → List Bool} {outputBit : List Bool → Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hargs : PolyTimeComputable args) (hcoins : PolyTimeComputable coins)
    (houtputBit : PolyTimeComputable fun z => [outputBit z]) (l : ℕ) (a : Fin l → Bool) :
    PolyTimeComputable (rowWordWith E₁ E₂ width bound inputs gate args coins outputBit l a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWord_poly

```lean
theorem rowWord_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs gate : List Bool → ℕ}
    {kind args coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hkind : PolyTimeComputable kind) (hargs : PolyTimeComputable args)
    (hcoins : PolyTimeComputable coins) (l : ℕ) (a : Fin l → Bool) :
    PolyTimeComputable (rowWord E₁ E₂ width bound inputs gate kind args coins l a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · assignmentBit_of_perm

```lean
theorem assignmentBit_of_perm (width bound gate : List Bool → ℕ)
    (coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool)
    (p : Equiv.Perm (Fin l → Bool)) (z : List Bool) (j : ℕ)
    (hp : ∀ t, p a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * gate z + t) false)) :
    assignmentBit width bound gate coins l a j z = (List.ofFn (p a)).getD j false
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · gateBit_eq_gateOut

```lean
theorem gateBit_eq_gateOut (g : DAGGate) (a : Fin g.args.length → Bool)
    (kind : List Bool → List Bool) (b₀ b₁ : List Bool → Bool) (z : List Bool)
    (hfan : g.args.length ≤ 2) (hkind : kind z = g.kind.encode)
    (h₀ : b₀ z = (List.ofFn a).getD 0 false)
    (h₁ : b₁ z = (List.ofFn a).getD 1 false) :
    gateBit kind g.args.length b₀ b₁ z = gateOut g a
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · assignmentFold_eq_two

```lean
theorem assignmentFold_eq_two {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 =
      ((List.ofFn a).getD 0 false).toNat + 2 * ((List.ofFn a).getD 1 false).toNat
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWordWith_enc

```lean
theorem rowWordWith_enc (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (args coins : List Bool → List Bool)
    (outputBit : List Bool → Bool)
    (z : List Bool) (C : DAGCircuit (inputs z))
    (s : GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (hfan : (C.gates[i]).args.length ≤ 2) (hgate : gate z = i)
    (hargs : args z = BinArith.encWords ((C.gates[i]).args.map fun v => List.replicate v true))
    (hkey : ∀ (v : ℕ), v < C.size → ∀ b,
      keyAt C s v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ a t, (s.2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * gate z + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ a t, (s.2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * gate z + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ a t, s.2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * gate z + t) false)) :
    rowWordWith E₁ E₂ width bound inputs gate args coins outputBit
        (C.gates[i]).args.length a z =
      (nestedSpecial E₁ E₂ (width z)).enc (argKeys C s i (s.2.2 i a))
        (keyAt C s (inputs z + i) (outputBit z)) (s.2.1 i (s.2.2 i a))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWord_garbledRow

```lean
theorem rowWord_garbledRow (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (z : List Bool) (C : DAGCircuit (inputs z))
    (s : GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (hfan : (C.gates[i]).args.length ≤ 2) (hgate : gate z = i)
    (hkind : kind z = (C.gates[i]).kind.encode)
    (hargs : args z = BinArith.encWords ((C.gates[i]).args.map fun v => List.replicate v true))
    (hkey : ∀ (v : ℕ), v < C.size → ∀ b,
      keyAt C s v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ a t, (s.2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * gate z + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ a t, (s.2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * gate z + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ a t, s.2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * gate z + t) false)) :
    rowWord E₁ E₂ width bound inputs gate kind args coins (C.gates[i]).args.length a z =
      garbledRow (nestedSpecial E₁ E₂ (width z)) C s i (s.2.2 i a)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWordWith_value

```lean
theorem rowWordWith_value (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (args coins : List Bool → List Bool)
    (outputBit : List Bool → Bool) (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWordWith E₁ E₂ width bound inputs gate args coins outputBit l a z =
      rowWordWith E₁ E₂ (fun _ => width z) (fun _ => bound z)
        (fun _ => inputs z) (fun _ => gate z) (fun _ => args z) (fun _ => coins z)
        (fun _ => outputBit z) l a []
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RowFromCoins.lean · rowWord_value

```lean
theorem rowWord_value (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWord E₁ E₂ width bound inputs gate kind args coins l a z =
      rowWord E₁ E₂ (fun _ => width z) (fun _ => bound z)
        (fun _ => inputs z) (fun _ => gate z) (fun _ => kind z)
        (fun _ => args z) (fun _ => coins z) l a []
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · step

```lean
def step (F : List Bool → List Bool) (w : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · step_eq

```lean
theorem step_eq (F : List Bool → List Bool) (w : List Bool) :
    step F w = pairEncode (pairSndD (pairFstD (pairSndD w)))
      (F (pairEncode (pairFstD w)
        (pairEncode (pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w)))))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · acc

```lean
def acc (w : List Bool) : Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · acc_eq

```lean
theorem acc_eq (w : List Bool) : acc w = decide (pairFstD (pairSndD w) = [])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · step_poly

```lean
theorem step_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (step F)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · acc_poly

```lean
theorem acc_poly : PolyTimeComputable fun w => [acc w]
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · orbit_eq

```lean
theorem orbit_eq {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    (F : List Bool → List Bool)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (x : List Bool) :
    ∀ i, i ≤ (gs x).length →
      StateLoop.orbit
          (fun z => pairEncode (BinArith.encWords ((gs z).map gateCode)) (valueCode z (init z)))
          (step F) x i =
        pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
          (valueCode x (runWith (f x) ((gs x).take i) (init x)))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · polyTimeComputable_runWith

```lean
theorem polyTimeComputable_runWith {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    {F : List Bool → List Bool}
    (hgs : PolyTimeComputable fun x => BinArith.encWords ((gs x).map gateCode))
    (hinit : PolyTimeComputable fun x => valueCode x (init x)) (hF : PolyTimeComputable F)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (R B : PolyExpr)
    (hN : ∀ x, (gs x).length ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ (gs x).length →
      (pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
        (valueCode x (runWith (f x) ((gs x).take i) (init x)))).length ≤ B.eval x.length) :
    PolyTimeComputable fun x => valueCode x (runWith (f x) (gs x) (init x))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean · exists_machine

```lean
theorem exists_machine {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    {F : List Bool → List Bool}
    (hgs : PolyTimeComputable fun x => BinArith.encWords ((gs x).map gateCode))
    (hinit : PolyTimeComputable fun x => valueCode x (init x)) (hF : PolyTimeComputable F)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (R B : PolyExpr)
    (hN : ∀ x, (gs x).length ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ (gs x).length →
      (pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
        (valueCode x (runWith (f x) ((gs x).take i) (init x)))).length ≤ B.eval x.length) :
    ∃ (M : FinTM Bool) (A d : ℕ),
      ModuleHost.Clean M (fun x => valueCode x (runWith (f x) (gs x) (init x)))
          (fun _ => []) (fun n => A * (n + 1) ^ d) ∧
        ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean · real_eq_stage0_on_tape

```lean
theorem real_eq_stage0_on_tape (r : Fin (10 * S * n + 2 * S) → Bool) :
    real r = GateHybridMessage.sample M C
      (seed (List.ofFn (CoinRelabel.relabel S n (CoinSeedRelabel.keyMask C S v)
        (CoinSeedRelabel.rowPerm C S hA v) (CoinSeedRelabel.shiftMask C S v) r)))
      inA inB outLen output v commonInput bobInput bobCoins aliceOutput 0
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean · acceptProb_real_eq_stage0

```lean
theorem acceptProb_real_eq_stage0 {κ : Type*} [Fintype κ]
    (D : List Bool → κ → Bool) :
    acceptProb real D = acceptProb
      (fun r : Fin (10 * S * n + 2 * S) → Bool =>
        GateHybridMessage.sample M C (seed (List.ofFn r)) inA inB outLen output v
          commonInput bobInput bobCoins aliceOutput 0) D
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean · acceptProb_real_eq_stage0_fst

```lean
theorem acceptProb_real_eq_stage0_fst {τ κ : Type*} [Fintype τ] [Nonempty τ]
    [Fintype κ] (D : List Bool → κ → Bool) :
    acceptProb (fun r : (Fin (10 * S * n + 2 * S) → Bool) × τ => real r.1) D =
      acceptProb (fun r : Fin (10 * S * n + 2 * S) → Bool =>
        GateHybridMessage.sample M C (seed (List.ofFn r)) inA inB outLen output v
          commonInput bobInput bobCoins aliceOutput 0) D
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean · distAdv_real_stage0_zero

```lean
theorem distAdv_real_stage0_zero {κ : Type*} [Fintype κ]
    (D : List Bool → κ → Bool) :
    distAdv real (fun r : Fin (10 * S * n + 2 * S) → Bool =>
      GateHybridMessage.sample M C (seed (List.ofFn r)) inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput 0) D = 0
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean · sample_end_of_result

```lean
theorem sample_end_of_result (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (result : Fin outLen → Bool) (hResult : ∀ j, v (output j) = result j)
    (commonInput bobInput bobCoins aliceOutput : List Bool) :
    GateHybridMessage.sample M C s inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput (2 * C.gates.length) =
      pairEncode (⟨commonInput,
        pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB)),
        bobCoins, [FakeObjects.message M C s inA outLen output result]⟩ : View).encode
        aliceOutput
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean · acceptProb_end_eq_fake

```lean
theorem acceptProb_end_eq_fake {σ κ : Type*} [Fintype σ] [Fintype κ]
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (seed : σ → GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (result : Fin outLen → Bool) (hResult : ∀ j, v (output j) = result j)
    (commonInput bobInput bobCoins aliceOutput : List Bool) (D : List Bool → κ → Bool) :
    acceptProb (fun r => GateHybridMessage.sample M C (seed r) inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput (2 * C.gates.length)) D =
      acceptProb (fun r => pairEncode (⟨commonInput,
        pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C (seed r) inA inB)),
        bobCoins, [FakeObjects.message M C (seed r) inA outLen output result]⟩ : View).encode
        aliceOutput) D
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean · acceptProb_end_eq_ideal

```lean
theorem acceptProb_end_eq_ideal {κ : Type*} [Fintype κ] (D : List Bool → κ → Bool) :
    acceptProb (fun r => GateHybridMessage.sample M C (seed r) inA inB outLen output v
      commonInput bobInput bobCoins aliceOutput (2 * C.gates.length)) D =
      acceptProb ideal D
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean · distAdv_end_ideal_zero

```lean
theorem distAdv_end_ideal_zero {κ : Type*} [Fintype κ] (D : List Bool → κ → Bool) :
    distAdv (fun r => GateHybridMessage.sample M C (seed r) inA inB outLen output v
      commonInput bobInput bobCoins aliceOutput (2 * C.gates.length)) ideal D = 0
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SimulationBound.lean · simulators_of_output_switch

```lean
theorem simulators_of_output_switch {G : Functionality} (H : HybridProtocol G)
    (F : Functionality) (SA SB : NUPPT)
    (switched : ∀ n, (Fin (F.inA.eval n) → Bool) → (Fin (F.inB.eval n) → Bool) →
      H.Coins n → List Bool)
    (δ : ℕ → ℝ) (hδ : Negligible δ)
    (hAlice : ∀ (D : NUPPT) n x y,
      distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ δ n)
    (hSwitch : ∀ n x y, StatClose (H.realB F n x y) (switched n x y) (δ n))
    (hBob : ∀ D : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n x y,
      distAdv (switched n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ μ n) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n x y,
      distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
        distAdv (H.realB F n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SimulationBound.lean · realB_output_switch

```lean
theorem realB_output_switch {G : Functionality} (H : HybridProtocol G)
    (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (Bad : H.Coins n → Prop) (δ : ℝ)
    (hBad : uprob Bad ≤ δ)
    (hOut : ∀ r, ¬ Bad r →
      H.main.outP (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r =
          List.ofFn (F.f n x y).1) :
    StatClose (H.realB F n x y)
      (fun r => pairEncode
        (H.main.viewV (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
        (List.ofFn (F.f n x y).1)) δ
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SimulationBound.lean · strategyTapeEquiv

```lean
def strategyTapeEquiv (S : Strategy) (n m : ℕ) (h : S.coinLen n = m) :
    S.Coins n ≃ (Fin m → Bool)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SimulationBound.lean · strategyTapeEquiv_eq

```lean
theorem strategyTapeEquiv_eq (S : Strategy) (n m : ℕ) (h : S.coinLen n = m) :
    strategyTapeEquiv S n m h = Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SimulationBound.lean · strategyTapeEquiv_ofFn

```lean
theorem strategyTapeEquiv_ofFn (S : Strategy) (n m : ℕ) (h : S.coinLen n = m)
    (r : S.Coins n) : List.ofFn (strategyTapeEquiv S n m h r) = List.ofFn r
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SimulationBound.lean · acceptProb_firstTape

```lean
theorem acceptProb_firstTape {G : Functionality} (H : HybridProtocol G) (n m : ℕ)
    (hLen : H.main.P.coinLen (List.replicate n true).length = m)
    (X : H.Coins n → List Bool) (Y : (Fin m → Bool) → List Bool)
    (hX : ∀ r, X r = Y (strategyTapeEquiv H.main.P (List.replicate n true).length m hLen r.1))
    {ρ : Type*} [Fintype ρ] (D : List Bool → ρ → Bool) :
    acceptProb X D = acceptProb Y D
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SliceReduction.lean · exists_adviceReduction

```lean
theorem exists_adviceReduction (D : NUPPT) {rebuild : List Bool → List Bool}
    (hRebuild : PolyTimeComputable rebuild) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ R : NUPPT, ∃ hcoins : R.coins = D.coins,
      ∀ n challenge (r : D.Coins n),
        R.distinguisherL n challenge (NUPPT.coinsCongr hcoins.symm n r) =
          D.distinguisherL n
            (rebuild (pairEncode (List.replicate n true) (pairEncode challenge (β n)))) r
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SliceReduction.lean · reconstruction_negligible

```lean
theorem reconstruction_negligible {L : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L.eval n) → Bool)}
    (hSecure : SliceMultiMessageSecure G) (D : NUPPT) (q b : PolyExpr)
    {A : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Nonempty (A n)]
    (advice : ∀ n, A n → List Bool) (hAdvice : ∀ n a, (advice n a).length ≤ b.eval n)
    {rebuild : List Bool → List Bool} (hRebuild : PolyTimeComputable rebuild)
    (offset len : ∀ n, A n → Fin (q.eval n + 1) → ℕ)
    (hFit : ∀ n a i, offset n a i + n + len n a i ≤ L.eval n)
    (m₀ m₁ : ∀ n a i, Fin (len n a i) → Bool) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n a,
      distAdv
        (fun t => rebuild (pairEncode (List.replicate n true)
          (pairEncode (sliceMultiEncDist G n (q.eval n) (offset n a) (len n a) (m₀ n a) t)
            (advice n a))))
        (fun t => rebuild (pairEncode (List.replicate n true)
          (pairEncode (sliceMultiEncDist G n (q.eval n) (offset n a) (len n a) (m₁ n a) t)
            (advice n a)))) (D.distinguisherL n) ≤ ε n
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SliceReduction.lean · distAdv_fibers_le

```lean
theorem distAdv_fibers_le {α β γ ρ : Type*} [Fintype α] [Fintype β] [Fintype ρ]
    (X Y : α → β → γ) (D : γ → ρ → Bool) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ a, distAdv (X a) (Y a) D ≤ ε) :
    distAdv (fun r : α × β => X r.1 r.2) (fun r : α × β => Y r.1 r.2) D ≤ ε
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SliceReduction.lean · distAdv_chain_le

```lean
theorem distAdv_chain_le {σ γ ρ : Type*} [Fintype σ] [Fintype ρ]
    (H : ℕ → σ → γ) (D : γ → ρ → Bool) (t : ℕ) (ε : ℝ)
    (h : ∀ i < t, distAdv (H i) (H (i + 1)) D ≤ ε) :
    distAdv (H 0) (H t) D ≤ (t : ℝ) * ε
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SliceReduction.lean · chain_negligible

```lean
theorem chain_negligible {I σ : ℕ → Type*} [∀ n, Fintype (σ n)]
    (H : ∀ n, I n → ℕ → σ n → List Bool) (D : NUPPT) (steps : ℕ → ℕ) (p : PolyExpr)
    (hSteps : ∀ n, steps n ≤ p.eval n) {μ : ℕ → ℝ} (hμ : Negligible μ)
    (h : ∀ n a i, i < steps n → distAdv (H n a i) (H n a (i + 1))
      (D.distinguisherL n) ≤ μ n) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n a,
      distAdv (H n a 0) (H n a (steps n)) (D.distinguisherL n) ≤ ε n
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/StatisticalSwitch.lean · statClose_of_eq_off

```lean
theorem statClose_of_eq_off {σ γ : Type*} [Fintype σ] (X Y : σ → γ)
    (Bad : σ → Prop) (δ : ℝ) (hBad : uprob Bad ≤ δ)
    (heq : ∀ r, ¬ Bad r → X r = Y r) : StatClose X Y δ
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/StatisticalSwitch.lean · distAdv_le_of_eq_off

```lean
theorem distAdv_le_of_eq_off {σ γ ρ : Type*} [Fintype σ] [Fintype ρ]
    (X Y : σ → γ) (Bad : σ → Prop) (δ : ℝ) (hBad : uprob Bad ≤ δ)
    (heq : ∀ r, ¬ Bad r → X r = Y r) (D : γ → ρ → Bool) :
    distAdv X Y D ≤ δ
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Strategies.lean · firstThenEcho_efficient

```lean
theorem firstThenEcho_efficient (S : Strategy)
    (first : List Bool → List Bool → List Bool → List Bool)
    (hNil : ∀ x z r, S.next x z r [] = first x z r)
    (hCons : ∀ x z r a hist, S.next x z r (a :: hist) = a)
    (hFirst : PolyTimeComputable fun w => first (GI.argX w) (GI.argZ w) (NUPPT.inCoins w)) :
    S.Efficient
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Strategies.lean · reply_efficient

```lean
theorem reply_efficient (S : Strategy)
    (reply : List Bool → List Bool → List Bool → List Bool)
    (hNext : ∀ x z r hist, S.next x z r hist = reply x z (hist.headD []))
    (hReply : PolyTimeComputable fun w =>
      reply (GI.argX w) (GI.argZ w) (pairFstD (GI.argM w))) : S.Efficient
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWordWith

```lean
noncomputable def tableWordWith (args : List Bool → List Bool)
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool) (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWordWith_eq

```lean
theorem tableWordWith_eq (args : List Bool → List Bool)
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool) (z : List Bool) :
    tableWordWith args row z =
      let count
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWord

```lean
noncomputable def tableWord (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (z : List Bool) : List Bool
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWord_eq

```lean
theorem tableWord_eq (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (z : List Bool) :
    tableWord E₁ E₂ width bound inputs gate kind args coins z =
      let count
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWordWith_poly

```lean
theorem tableWordWith_poly {args : List Bool → List Bool}
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool)
    (hargs : PolyTimeComputable args)
    (hrow : ∀ l, l ≤ 2 → ∀ a, PolyTimeComputable (row l a)) :
    PolyTimeComputable (tableWordWith args row)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWord_poly

```lean
theorem tableWord_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs gate : List Bool → ℕ}
    {kind args coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hkind : PolyTimeComputable kind) (hargs : PolyTimeComputable args)
    (hcoins : PolyTimeComputable coins) :
    PolyTimeComputable (tableWord E₁ E₂ width bound inputs gate kind args coins)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWordWith_of_encoded

```lean
theorem tableWordWith_of_encoded (args : List Bool → List Bool)
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool) (z : List Bool)
    (vertices : List ℕ) (hfan : vertices.length ≤ 2)
    (hargs : args z = BinArith.encWords (vertices.map fun v => List.replicate v true)) :
    tableWordWith args row z = BinArith.encWords
      ((Finset.univ : Finset (Fin vertices.length → Bool)).toList.map fun a =>
        row vertices.length a z)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWord_garbledTable

```lean
theorem tableWord_garbledTable (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (z : List Bool) (C : DAGCircuit (inputs z))
    (s : GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : Fin C.gates.length) (hfan : (C.gates[i]).args.length ≤ 2)
    (hargs : args z = BinArith.encWords ((C.gates[i]).args.map fun v => List.replicate v true))
    (hrow : ∀ a,
      RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind args coins
          (C.gates[i]).args.length a z =
        garbledRow (nestedSpecial E₁ E₂ (width z)) C s i (s.2.2 i a)) :
    tableWord E₁ E₂ width bound inputs gate kind args coins z =
      BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) C s i)
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TablesFromCoins.lean · tableWordWith_congr_at

```lean
theorem tableWordWith_congr_at (args args' : List Bool → List Bool)
    (row row' : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool) (z z' : List Bool)
    (hargs : args z = args' z') (hrow : ∀ l a, row l a z = row' l a z') :
    tableWordWith args row z = tableWordWith args' row' z'
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · transcriptWith_eq

```lean
theorem transcriptWith_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.transcriptWith π.P w zA zB r =
      ([msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))],
        [msgA w zA (List.ofFn r.1)])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · transcript_eq

```lean
theorem transcript_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.transcript w zA zB r =
      ([msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))],
        [msgA w zA (List.ofFn r.1)])
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · viewP_eq

```lean
theorem viewP_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.viewP w zA zB r =
      ⟨w, zA, List.ofFn r.1,
        [msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))]⟩
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · viewV_eq

```lean
theorem viewV_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.viewV w zA zB r = ⟨w, zB, List.ofFn r.2, [msgA w zA (List.ofFn r.1)]⟩
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · encode_viewP_eq

```lean
theorem encode_viewP_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    (π.viewP w zA zB r).encode =
      pairEncode (pairEncode w zA) (pairEncode (List.ofFn r.1)
        (Strategy.encodeMsgs [msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))]))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · encode_viewV_eq

```lean
theorem encode_viewV_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    (π.viewV w zA zB r).encode =
      pairEncode (pairEncode w zB)
        (pairEncode (List.ofFn r.2) (Strategy.encodeMsgs [msgA w zA (List.ofFn r.1)]))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · outV_eq

```lean
theorem outV_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.outV π.P w zA zB r =
      msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · outP_eq

```lean
theorem outP_eq (hEcho : ∀ w z r b, π.P.next w z r [b] = b)
    (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.outP w zA zB r = msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · realA_eq

```lean
theorem realA_eq (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n) :
    H.realA F n x y r =
      let w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TwoMoveViews.lean · realB_eq

```lean
theorem realB_eq (hEcho : ∀ w z r b, H.main.P.next w z r [b] = b)
    (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n) :
    H.realB F n x y r =
      let w
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/WordLists.lean · rangeTable_poly

```lean
theorem rangeTable_poly {count : List Bool → ℕ} {entry : List Bool → ℕ → List Bool}
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hentry : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length) :
    PolyTimeComputable fun z =>
      BinArith.encWords ((List.range (count z)).map (entry z))
```

## TCSlib/Cryptography/SecureComputation/Yao/HybridProof/WordLists.lean · ofFnTable_poly

```lean
theorem ofFnTable_poly {count : List Bool → ℕ} (f : ∀ z, Fin (count z) → List Bool)
    (entry : List Bool → ℕ → List Bool)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hentry : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length)
    (hf : ∀ z i, f z i = entry z i) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn (f z))
```
