<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: boolToSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bits to signs

**Definition.** `boolToSign (b : Bool) : ℝ := if b then -1 else 1` — the bridge
from the bit picture to the sign picture, `false ↦ 1` and `true ↦ -1`. Reading
`true` as the bit `1`, this is exactly `(-1)^b`.

Its whole interface is four `simp` lemmas, all proved by `cases b <;> simp
[boolToSign]`:

- `boolToSign_false = 1` and `boolToSign_true = -1` (both `rfl`);
- `boolToSign_sq : boolToSign b ^ 2 = 1`;
- `boolToSign_mul_self : boolToSign b * boolToSign b = 1`;
- `boolToSign_not : boolToSign (!b) = -boolToSign b`.

**Remark.** That the square *and* the self-product both reduce to `1` is what
makes the Walsh characters unimodular and self-cancelling: it drives
`chiS_sq_eq_one` and the `P * P = 1` cancellation at the heart of
`chiS_mul_chiS` (`χ_S · χ_T = χ_{S Δ T}`), where the shared `S ∩ T` factor is
squared away.

**Used in.** `chiS S x = ∏ i ∈ S, boolToSign (x i)`, hence — transitively —
every Fourier coefficient, Parseval statement and influence bound in the layer.
`boolToSign_not` is the coordinate-level input to `chiS_neg`.
