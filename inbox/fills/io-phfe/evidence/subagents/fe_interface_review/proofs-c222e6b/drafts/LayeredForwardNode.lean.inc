/-- A non-root prefix's forward value is its parent's value times its final edge
weight. This is a technical recurrence for the layered path-sum specialization of
[AGW20, Appendix A, (32), p.38].

**Proof sketch.** Apply the published node, parent, edge-label and forward readers.
Split the final factor with Fin.prod_univ_castSucc; Fin.init_def identifies the
remaining product with the parent's path value. -/
theorem forward_node (x : Fin l → ZMod (p : ℕ)) (v : TIdx l d) :
    forward x (node v) = forward x (parent v) * xhat x (lastLabel v) := by
  simpa only [node_eq, parent_eq, lastLabel_eq, forward_eq, Fin.val_succ,
    Fin.coe_castSucc, Fin.init_def] using
    (Fin.prod_univ_castSucc (fun i : Fin (v.1.val + 1) => xhat x (v.2 i)))
