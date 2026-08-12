<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: flipBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Flipping one coordinate

**Definition.** `flipBit (x : BoolCube n) (i : Fin n) : BoolCube n :=
Function.update x i (!x i)` — the point written `xⁱ` in the literature: `x` with
coordinate `i` negated and every other coordinate untouched.

Defining it through `Function.update` rather than by a hand-rolled `if` buys the
whole Mathlib `update` API, and the two facts that characterise it come out in
one line each:

- `flipBit_flipBit : flipBit (flipBit x i) i = x` — it is an involution
  (marked `@[simp]`);
- `flipBit_ne : i ≠ j → flipBit x i j = x j` — off the flipped coordinate
  nothing moves, by `Function.update_of_ne`.

**Remark.** `flipBit` is a `def`, not `noncomputable`: negating one bit needs no
choice, so it computes, even though the expectations taken over it do not.

**Used in.** The definition of `influence i f = expect (fun x ↦ (f x - f (flipBit
x i)) ^ 2 / 4)`, hence `totalInfluence`; and the private lemma `chiS_flipBit`
(`chiS S (flipBit x i) = if i ∈ S then -chiS S x else chiS S x`), which is the
step that converts influence into Fourier weight in `influence_chi` and
`totalInfluence_eq_sum_sq_deg`. All consumers are inside `Basic.lean`.
