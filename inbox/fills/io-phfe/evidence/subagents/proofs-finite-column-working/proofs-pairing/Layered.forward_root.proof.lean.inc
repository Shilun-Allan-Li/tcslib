/-- The source's forward value is the empty product 1.

**Proof sketch.** The root tuple has domain Fin 0; its finite product is empty. -/
theorem forward_root (x : Fin l → ZMod (p : ℕ)) : forward x (root l d) = 1 :=
  (congrArg (forward (d := d) x) (root_eq l d)).trans
    ((forward_eq x
      (⟨⟨0, Nat.zero_lt_succ d⟩, Fin.elim0⟩ : MIdx l d)).trans
      (Fin.prod_univ_zero (fun i : Fin 0 => xhat x (Fin.elim0 i))))
