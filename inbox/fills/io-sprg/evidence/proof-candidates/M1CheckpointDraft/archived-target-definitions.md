## Phase B target statements (unproved)

These are the exact frozen definitions, with parameters in their enclosing Params namespace.

### T1

```lean
def evalTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (sd : P.Seed κ pp),
      f (NUPPT.advInput κ (pairEncode pp.enc
        (pairEncode (P.encIdx' κ pp I) (P.encSeed' κ pp sd)))) =
          List.ofFn (P.eval' κ pp I sd)
```

### T2

```lean
def qGenTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (j : Fin (P.m κ)),
      ∃ ts : PolyTerms (Fin (P.pubLen κ) ⊕ Fin (P.privLen κ)) (ZMod pp.p),
        f (NUPPT.advInput κ (pairEncode pp.enc
          (pairEncode (P.encIdx' κ pp I) (PolyTerms.encFin j)))) =
            PolyTerms.encTerms (fun z => Candidates.natToList (κ + 1) z.val)
              (fun v => PolyTerms.encFin (finSumFinEquiv v)) ts ∧
        PolyTerms.denote ts = P.G4 κ pp I j
```

### T3

```lean
def coreTarget (P : Params) : Prop :=
  CoreComputable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp)
      (fun κ pp => P.encIdx' κ pp) (fun κ pp => P.idCore κ pp) ∧
    CoreComputable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)
      (fun κ q => P.encSeed' κ q.1)
      (fun κ q d => (P.sdCore κ q.1 q.2 d).seed)
```

### T4

```lean
def lpnPreTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ (π : PrimeSchedule) L (ω : P.LPNAdvice π L) (x : P.LPNChal π L),
      f (pairEncode (P.encLPNAdvice π L ω) (P.lpnEnc π L x)) = P.lpnPre π L ω x

def prgPreTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ (π : PrimeSchedule) N (ω : P.PRGAdvice π N) (x : P.PRGChal N),
      f (pairEncode (P.encPRGAdvice π N ω) (P.prgEnc N x)) = P.prgPre π N ω x

def ReductionTargets (P : Params) : Prop :=
  P.lpnPreTarget ∧ P.prgPreTarget
```

### T5

```lean
def drawSamplerTarget (P : Params) : Prop :=
  DrawSamplable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp) ∧
    DrawSamplable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)
```

### T6

```lean
def lpnSamplerTarget (P : Params) : Prop :=
  SamplesEfficiently (P := fun _ => PrimeSchedule)
    (fun L π => (P.lpnFamily_raw π).sampleWord L)
    (fun L π => (P.lpnFamily_raw π).encDraw L)
    (fun L π => (P.lpnFamily_raw π).encSample L)
    (fun L π => (P.lpnFamily_raw π).sampleCore L)
```

### Conjunction

```lean
def Targets (P : Params) : Prop :=
  P.evalTarget ∧ P.qGenTarget ∧ P.coreTarget ∧ P.ReductionTargets ∧
    P.drawSamplerTarget ∧ P.lpnSamplerTarget
```
