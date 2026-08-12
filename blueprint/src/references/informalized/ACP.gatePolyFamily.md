<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: gatePolyFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A chosen approximator family for one gate

**Definition.** For `n ℓ : ℕ`, a gate operation `op : GateOp (Fin 2)` and a proof
`hop : op ∈ ACp_GateOps p`,
`gatePolyFamily p n ℓ op hop : GatePolyFamily p n ℓ op` is
`Classical.choose (exists_gate_poly_family (p := p) n ℓ op hop)`.

A plain definition; no proof. It turns the existence statement
`exists_gate_poly_family` into a usable term, so the layer construction can *name*
one approximator family per gate rather than repeatedly destructuring an
existential. `noncomputable`, since `Classical.choose` is.

**Remark.** Nothing about the chosen family is accessible beyond the fields of the
`GatePolyFamily` structure: a seed type `Seed` (finite, decidable equality,
nonempty), a polynomial `poly polys s`, the degree bound
`(poly polys s).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree`, and the
bad-seed bound `(#bad seeds) * 2 ^ ℓ ≤ Fintype.card Seed` on Boolean-valued
inputs. That opacity is deliberate — the layer induction is uniform in the gate.

**Used in.** `stepLayerFamily`, where
`Fam u := gatePolyFamily (p := p) n ℓ ((F.gates dF u).op) (hUses dF u)` supplies one
family per node of the next layer, and the new seed type is the product of the
`(Fam u).Seed` over all such `u`.

<!-- ------------------------------------------------------------------ -->
<!-- NOTE: this file documents TWO declarations. `ACP.GatePolyFamily`   -->
<!-- (the structure) and `ACP.gatePolyFamily` (the def chosen from it)  -->
<!-- differ only by leading case, and this filesystem is case-          -->
<!-- insensitive, so they cannot have separate note files. Both are     -->
<!-- kept here; the structure's note follows.                           -->
<!-- ------------------------------------------------------------------ -->

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: GatePolyFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Approximator family for a single gate

**Definition.** `GatePolyFamily p n ℓ op` is a structure packaging a randomized
polynomial approximation of one gate `op : GateOp (Fin 2)` in `n` variables with
error parameter `ℓ`. Its fields:

- `Seed : Type`, with instance fields `seedFintype : Fintype Seed` and
  `seedDecEq : DecidableEq Seed` (registered globally by
  `attribute [instance] GatePolyFamily.seedFintype GatePolyFamily.seedDecEq`);
- `card_pos : 0 < Fintype.card Seed`;
- `poly : (op.ι → MvPolynomial (Fin n) (ZMod p)) → Seed → MvPolynomial (Fin n) (ZMod p)`,
  producing an approximating polynomial from the gate's incoming polynomials and a
  seed;
- `degree`: for all `polys` and `s`,
  `(poly polys s).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree`;
- `bad`: for all `polys` and every Boolean input `x`, writing
  `y = boolInput (p := p) x` and `inputs i = (polys i).eval y`, if every
  `inputs i ∈ ({0, 1} : Set (ZMod p))` then
  `#{s : Seed | (poly polys s).eval y ≠ ((op.func (fun i => bitify (p := p) (inputs i)) : Nat) : ZMod p)} * 2 ^ ℓ ≤ Fintype.card Seed`
  — at most a `2^{-ℓ}` fraction of seeds misrepresent the gate at that input.

**Remark.** The point of the bundling (as the docstring says) is that `Seed`
depends only on the gate, not on its incoming polynomials; that independence is
what lets `stepLayerFamily` form the product seed `A.Seed × ((u : nodes) → (Fam u).Seed)`
over a whole layer at once. `exists_gate_poly_family` produces one instance for
every `op ∈ ACp_GateOps p` (identity, NOT, unbounded AND via `approxAnd`,
`MOD p` via `exactMod`), and `gatePolyFamily` picks one with `Classical.choose`.
