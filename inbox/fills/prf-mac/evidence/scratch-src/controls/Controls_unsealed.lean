import TCSlib.Cryptography.Authentication.MAC.FromPRF

/-! Paired Rule-10 seal controls of the prf-mac fill. Each `CONTROL` example reads a foreign
definition by `rfl` (a negative: it must close unsealed and fail exactly once sealed); each
`READER` example proves the same fact through the published reader (it must close sealed); the
`PROBE` records how the projection-coercion instance behaves under the two seal variants. The
line `-- (no seal)` is replaced by the seal harness of the variant. -/

-- (no seal)

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Authentication

-- CONTROL C1 (Games.InteractiveHandler.rAns)
example (w : List Bool) :
    InteractiveHandler.rAns w = pairSndD (pairSndD (pairFstD (InteractiveHandler.rL w))) := rfl
-- READER C1
example (w : List Bool) :
    InteractiveHandler.rAns w = pairSndD (pairSndD (pairFstD (InteractiveHandler.rL w))) :=
  InteractiveHandler.rAns_eq w

-- CONTROL C2 (PRFMAC.macBudget, a helper definition)
example (q : PolyExpr) (n : ℕ) : (PRFMAC.macBudget q).eval n =
    q.eval n * (PolyExpr.const 1).eval n + (PolyExpr.const 1).eval n := rfl
-- READER C2
example (q : PolyExpr) (n : ℕ) : (PRFMAC.macBudget q).eval n =
    q.eval n * (PolyExpr.const 1).eval n + (PolyExpr.const 1).eval n := PRFMAC.macBudget_eval q n

-- CONTROL C3 (PRFMAC.fnImpl, a helper definition)
example (f : (Fin 2 → Bool) → (Fin 3 → Bool)) (x : Fin 2 → Bool) :
    PRFMAC.fnImpl f 0 x () = .pure (f x, ()) := rfl
-- READER C3
example (f : (Fin 2 → Bool) → (Fin 3 → Bool)) (x : Fin 2 → Bool) :
    PRFMAC.fnImpl f 0 x () = .pure (f x, ()) := PRFMAC.fnImpl_apply f 0 x ()

-- CONTROL C4 (MAC.forgerCodec)
example (M : MAC) (n : ℕ) : M.forgerCodec n = bitCodec (fun _ : Fin 1 => M.msgLen.eval n)
    (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n) := rfl
-- READER C4
example (M : MAC) (n : ℕ) : M.forgerCodec n = bitCodec (fun _ : Fin 1 => M.msgLen.eval n)
    (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n) :=
  PRFMAC.forgerCodec_eq_bitCodec M n

-- CONTROL C5 (PolyExpr.eval: closes when it is notation, fails when it is sealed)
example (ℓ t : PolyExpr) (n : ℕ) : (PolyExpr.add ℓ t).eval n = ℓ.eval n + t.eval n := rfl
-- READER C5
example (ℓ t : PolyExpr) (n : ℕ) : (PolyExpr.add ℓ t).eval n = ℓ.eval n + t.eval n :=
  PolyExpr.eval_add ℓ t n

-- PROBE C6 (FinDist's projection coercion, read through its instance: the only request in which the
-- strict and coe variants differ; recorded, not a control)
example {α : Type} [Fintype α] (d : TCSlib.InformationTheory.FinDist α) (a : α) :
    (TCSlib.InformationTheory.FinDist.instCoeFunForallReal (α := α)).coe d a = d.prob a := rfl

-- CONTROL C7 (PRFMAC.macHandler, a helper definition)
example (q ℓ t : PolyExpr) : (PRFMAC.macHandler q ℓ t).perCall = .const 1 := rfl
-- READER C7
example (q ℓ t : PolyExpr) : (PRFMAC.macHandler q ℓ t).perCall = .const 1 :=
  PRFMAC.macHandler_perCall q ℓ t
