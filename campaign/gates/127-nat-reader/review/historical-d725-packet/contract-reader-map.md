# Exact private Nat.bit reader change

The complete formal header stays:

```lean
private lemma canonOffset_spec (w : List Bool) :
    Nat.ofDigits 2 ((canonOffset w).map Bool.toNat) = 2 * w.length + 3 ∧
      (canonOffset w).length ≤ w.length + 2
```

Only `simp [Nat.bit]` becomes `simp only [Nat.bit_val, Bool.toNat_true]`.
All preceding canonical-counter equations and the entire length branch remain
byte exact. The public Mathlib equation has orientation
`Nat.bit b n = 2*n + b.toNat`; specializing `b=true` exposes `2*n+1` without
explicitly unfolding the foreign `Nat.bit` definition. The existing `omega`
step closes the resulting arithmetic. No canonizer definition, output contract,
length bound, import, name or other proof step changes.

The exact whole-source reversal is checked, and the private declaration's
compiled full raw type, universes, kernel/module, privacy/kind, simp flags and
AX are exact to BASE. Full matching23-module replay supplies actual-owner
validation. The independent guarded example tests only this public Mathlib
reader, with two same-identity positive/negative controls. It does not seal the
complete private proof: unchanged explicit own canonizer equations remain in
its other branch. The pinned7295-byte Mathlib source is included at
`inputs/nat-reader/Mathlib-BinaryRec.lean.txt`, `Nat.bit_val:93`.
