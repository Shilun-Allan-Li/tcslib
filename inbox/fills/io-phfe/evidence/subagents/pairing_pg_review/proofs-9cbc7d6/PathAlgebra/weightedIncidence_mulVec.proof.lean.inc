/-- A weighted endpoint row acts on node values by taking its weighted parent
value minus its child value. No injectivity or distinctness of endpoints is required.

**Proof sketch.** Identify each row with the difference of its parent and child
coordinate vectors. Apply the published subtraction and single-coordinate
dot-product laws; the child coefficient is 1. -/
theorem weightedIncidence_mulVec {V E R : Type*} [Fintype V] [DecidableEq V]
    [Ring R] (parent child : E → V) (weight : E → R) (values : V → R) :
    Matrix.mulVec
      (Matrix.of fun e v =>
        (if v = parent e then weight e else 0) -
          (if v = child e then 1 else 0)) values =
      fun e => weight e * values (parent e) - values (child e) :=
  funext fun e =>
    show dotProduct
      (fun v => (if v = parent e then weight e else 0) -
        (if v = child e then 1 else 0)) values =
        weight e * values (parent e) - values (child e) from
      (congrArg (fun row : V → R => dotProduct row values)
        (funext fun v =>
          congrArg₂ (fun a b : R => a - b)
            (Pi.single_apply (parent e) (weight e) v).symm
            (Pi.single_apply (child e) (1 : R) v).symm)).trans
        ((sub_dotProduct (Pi.single (parent e) (weight e))
          (Pi.single (child e) (1 : R)) values).trans
          (congrArg₂ (fun a b : R => a - b)
            (single_dotProduct values (weight e) (parent e))
            (single_one_dotProduct (child e) values)))
