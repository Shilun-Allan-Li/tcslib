import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRelabel

open TCSlib.Cryptography
open TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel

-- The shift coordinate remains well typed and exact at zero key length.
example (S : ℕ) (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4))
    (mask : Fin S → Fin 2 → Bool) (r : Fin (10 * S * 0 + 2 * S) → Bool)
    (i : Fin S) (t : Fin 2) :
    (List.ofFn (relabel S 0 values rows mask r)).getD (10 * S * 0 + 2 * i + t) false =
      xor ((List.ofFn r).getD (10 * S * 0 + 2 * i + t) false) (mask i t) :=
  relabel_shift_getD S 0 values rows mask r i t

-- The complete inverse law includes the empty S=0 tape.
example (n : ℕ) (values : Fin 0 → Bool) (rows : Fin 0 → Equiv.Perm (Fin 4))
    (mask : Fin 0 → Fin 2 → Bool) (r : Fin (10 * 0 * n + 2 * 0) → Bool) :
    (relabel 0 n values rows mask).symm (relabel 0 n values rows mask r) = r :=
  (relabel 0 n values rows mask).symm_apply_apply r

-- The probability interface is the existing public change-of-coins theorem.
example (S n : ℕ) (values : Fin S → Bool) (rows : Fin S → Equiv.Perm (Fin 4))
    (mask : Fin S → Fin 2 → Bool) (p : (Fin (10 * S * n + 2 * S) → Bool) → Prop) :
    uprob (fun r => p (relabel S n values rows mask r)) = uprob p :=
  uprob_comp_equiv (relabel S n values rows mask) p
