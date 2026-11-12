import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF

/-! Seal controls of the pk-cpa-cca1 fill (unsealed: every example must pass): twelve readings
through a definition body. -/

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Composability.PRFGame

-- Control 1: `PolyExpr.eval` through its body.
example (n : ℕ) : (PolyExpr.var.add PolyExpr.var).eval n = n + n := rfl
-- Control 2: `FixedLengthScheme.outLens` through its body.
example (S : FixedLengthScheme) (n : ℕ) : S.outLens n 0 = S.ctLen.eval n := rfl
-- Control 3: `OracleComp.CostBoundedBy` through its body.
example {ι : Type} {spec : OracleSpec ι} {α : Type} (i : ι) (x : spec.dom i)
    (k : spec.rng i → OracleComp spec α) (m : ℕ)
    (h : (OracleComp.query i x k).CostBoundedBy (fun _ => 1) m) : 1 ≤ m := h.1
-- Control 4: `simulate` through its body.
example {ι : Type} {spec : OracleSpec ι} {σ α : Type} (impl : QueryImpl spec σ unifSpec)
    (a : α) (s : σ) : simulate impl (OracleComp.pure a) s = .pure (a, s) := rfl
-- Control 5: `FixedLengthScheme.INDSecure` through its body.
example (S : FixedLengthScheme) (h : S.INDSecure .cpa) (A : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, advantage (S.indGame .cpa A (q.eval n) false n)
      (S.indGame .cpa A (q.eval n) true n) ≤ ε n := h A q
-- Control 6: the new helper `atkOf` through its body.
example : atkOf false = .cpa := rfl
-- Control 7: the new helper `fImpl` through its body.
example (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack) (b : Bool)
    (f : (Fin n → Bool) → (Fin n → Bool)) (mm : Fin (ins 2) → Bool) (c : Fin d → Bool) :
    fImpl ins outs d n atk b f 2 mm (some c) = .pure (padFin _ (List.ofFn c), some c) := rfl
-- Control 8: the new helper `pkHandler` through its body.
example (q : PolyExpr) (atkBit b : Bool) : (pkHandler q atkBit b).finCall = .const 0 := rfl
-- Control 9: the new helper `pkHState` through its body.
example (q : PolyExpr) (atkBit b : Bool) (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    pkHState q atkBit b n j o = pkState q n j o := rfl
-- Control 10: the new helper `look` through its body.
example (n d : ℕ) (b : Bool) (T : List ((Fin n → Bool) × (Fin n → Bool))) (bd : Bool)
    (x : Fin n → Bool) : look b ((T, none, bd) : LState n d) x = T.lookup x := rfl
-- Control 11: the new helper `addPt` through its body.
example (n d : ℕ) (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    (addPt b st x y hit).2.2 = (st.2.2 || hit) := rfl
-- Control 12: the new helper `lazyImpl` through its body.
example (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack) (b : Bool) (mm : Fin (ins 2) → Bool)
    (T : List ((Fin n → Bool) × (Fin n → Bool))) (ml : List Bool) (c : Fin d → Bool) (bd : Bool) :
    lazyImpl ins outs d n atk b 2 mm (T, some (ml, c), bd) =
      .pure (padFin _ (List.ofFn c), (T, some (ml, c), bd)) := rfl
