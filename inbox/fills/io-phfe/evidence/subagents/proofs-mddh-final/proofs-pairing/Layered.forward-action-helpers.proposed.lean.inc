-- Proposed additions only. Bodies are deliberately unproved search placeholders.
-- Do not import these declarations into the search probe; that would trivialize exact?.

/-- A non-root prefix's forward value is its parent's value times its final edge
weight. This is a technical recurrence for the layered path-sum specialization of
[AGW20, Appendix A, (32), p.38].

**Proof sketch.** Apply the published node, parent, edge-label and forward readers.
Split the final factor with Fin.prod_univ_castSucc; Fin.init_def identifies the
remaining product with the parent's path value. -/
theorem forward_node (x : Fin l → ZMod (p : ℕ)) (v : TIdx l d) :
    forward x (node v) = forward x (parent v) * xhat x (lastLabel v) := sorry

/-- A non-root input-matrix row has its padded edge weight at the parent and a
negative unit at its node. This is the layered incidence formula of
[AGW20, Appendix A, (32), p.38].

**Proof sketch.** Read matrix, L1, L0 and publicTensor through their published
entry equations. Split the product-index sum and collapse its matching node
coordinate. Fin.lastCases separates a variable edge from the padded constant;
the two padding readers give the displayed weight. -/
theorem matrix_inl (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (v : TIdx l d) (u : MIdx l d) :
    matrix C x (Sum.inl v) u =
      (if u = parent v then xhat x (lastLabel v) else 0) -
        (if u = node v then 1 else 0) := sorry
