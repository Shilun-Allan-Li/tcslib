import TCSlib.Cryptography.SecureComputation.ComposeSecurity

/-! Paired Rule-10 seal controls of the sc-compose fill. Each `CONTROL` example reads a definition
foreign to this file by `rfl` (a negative: it must close unsealed and fail exactly once sealed);
each `READER` example proves the same fact through the published reader (it must close sealed).
The line `-- SEAL-HERE` is replaced by the seal harness of the variant. -/

-- SEAL-HERE

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.SecureComputation

-- CONTROL C1 (ComposeSim.segW, an Assembly.lean definition)
example (vF b : Bool) (R : ℕ) (e : List Bool) :
    ComposeSim.segW vF b R e = (List.range R).flatMap fun p =>
      pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) [] := rfl
-- READER C1
example (vF b : Bool) (R : ℕ) (e : List Bool) :
    ComposeSim.segW vF b R e = (List.range R).flatMap fun p =>
      pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) [] :=
  ComposeSim.segW_eq vF b R e

-- CONTROL C2 (ComposeSim.tmplW, a Template.lean definition)
example (hdr out : List Bool) (pre suf : List (List Bool)) :
    ComposeSim.tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
      (pairEncode (Strategy.encodeMsgs suf) out) := rfl
-- READER C2
example (hdr out : List Bool) (pre suf : List (List Bool)) :
    ComposeSim.tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
      (pairEncode (Strategy.encodeMsgs suf) out) :=
  ComposeSim.tmplW_eq hdr pre suf out

-- CONTROL C3 (HybridProtocol.inA, a Runs.lean definition)
example {G : Functionality} (H : HybridProtocol G) (n : ℕ) (zA rA : List Bool) (j : ℕ) :
    H.inA n zA rA j =
      if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else [] := rfl
-- READER C3
example {G : Functionality} (H : HybridProtocol G) (n : ℕ) (zA rA : List Bool) (j : ℕ) :
    H.inA n zA rA j =
      if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else [] :=
  H.inA_eq n zA rA j

-- CONTROL C4 (ComposeProb.hybV, a Chain.lean definition)
example {M X S : Type} {L : ℕ} (real : M → Fin L → X → List Bool)
    (sim : M → Fin L → S → List Bool) (i : ℕ) (ω : M × (Fin L → X × S)) (j : ℕ) :
    ComposeProb.hybV real sim i ω j =
      if h : j < L then
        (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).1)
      else [] := rfl
-- READER C4
example {M X S : Type} {L : ℕ} (real : M → Fin L → X → List Bool)
    (sim : M → Fin L → S → List Bool) (i : ℕ) (ω : M × (Fin L → X × S)) (j : ℕ) :
    ComposeProb.hybV real sim i ω j =
      if h : j < L then
        (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).1)
      else [] :=
  ComposeProb.hybV_eq real sim i ω j

-- CONTROL C5 (HybridProtocol.viewRunA, a SideA.lean definition)
example {G : Functionality} (H : HybridProtocol G) (ρ : Protocol) (n : ℕ) (xs ys : List Bool)
    (m : H.Coins n) (j : Fin (H.calls.eval n)) (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
      (H.inB n ys (List.ofFn m.2) j) t).encode := rfl
-- READER C5
example {G : Functionality} (H : HybridProtocol G) (ρ : Protocol) (n : ℕ) (xs ys : List Bool)
    (m : H.Coins n) (j : Fin (H.calls.eval n)) (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
      (H.inB n ys (List.ofFn m.2) j) t).encode :=
  H.viewRunA_eq ρ n xs ys m j t

-- CONTROL C6 (HybridProtocol.answersA, a definition of the frozen Hybrid.lean)
example {G : Functionality} (H : HybridProtocol G) (n : ℕ) (x y rA rB : List Bool) :
    H.answersA n x y rA rB = (List.ofFn fun j : Fin (H.calls.eval n) =>
      List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).1).flatten := rfl
-- READER C6
example {G : Functionality} (H : HybridProtocol G) (n : ℕ) (x y rA rB : List Bool) :
    H.answersA n x y rA rB = (List.ofFn fun j : Fin (H.calls.eval n) =>
      List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).1).flatten :=
  H.answersA_eq n x y rA rB

-- CONTROL C7 (PolyExpr.eval: closes when it is notation, fails when it is sealed)
example (p q : PolyExpr) (n : ℕ) : (PolyExpr.add p q).eval n = p.eval n + q.eval n := rfl
-- READER C7
example (p q : PolyExpr) (n : ℕ) : (PolyExpr.add p q).eval n = p.eval n + q.eval n :=
  PolyExpr.eval_add p q n
