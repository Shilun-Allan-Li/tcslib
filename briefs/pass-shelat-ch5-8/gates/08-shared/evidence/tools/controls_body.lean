open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates NumberTheory

namespace S1Unsealed
-- C1 natToList by its body
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
-- C2 listToNat by its body
example (w : List Bool) : listToNat w = w.foldl (fun a c => 2 * a + if c then 1 else 0) 0 := rfl
-- C3 rejectBlocksL by its body
example (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
      else none := rfl
-- C4 StatClose by its body
example (X Y : Fin 2 → ℕ) (δ : ℝ) :
    StatClose X Y δ ↔ ∀ T : ℕ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ :=
  Iff.rfl
-- C5 uexp by its body
example (f : Fin 3 → ℝ) : uexp f = (∑ a, f a) / Fintype.card (Fin 3) := rfl
-- C6 PushesUniform by its body
example (π : Fin 2 → Fin 2) :
    HardcoreBit.PushesUniform π ↔ ∀ F : Fin 2 → ℝ, uexp (fun ω => F (π ω)) = uexp F := Iff.rfl
-- C7 PolyTimeComputable by its body
example (f : List Bool → List Bool) : PolyTimeComputable f ↔
    ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c := Iff.rfl
-- C8 sampleUnitL by its body
example (N k B T : ℕ) (r : List Bool) :
    sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r := rfl
-- C9 subStr by its body
example (z : List Bool) : subStr z =
    natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z)) := rfl
-- C10 the repetition host's matcher against a local match on the same discriminant
example (o : Option ℕ) (a : ℕ → List Bool) (b : List Bool) :
    Complexity.polyTimeComputable_iterateFind.match_1 (fun _ => List Bool) o (fun i => a i) (fun _ => b) =
      (match o with | some i => a i | none => b) := rfl
-- C11 sampleBelowL by its body
example (m k B T : ℕ) (r : List Bool) : sampleBelowL m k B T r = (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none := rfl
-- C12 bitsToNat by its body
example (b : Fin 3 → Bool) :
    bitsToNat b = (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := rfl
-- C13 mulStr by its body
example (z : List Bool) : mulStr z = natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) * listToNat (pairSndD z)) := rfl
end S1Unsealed
