<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: Literal.flipNeg_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Polarity flipping is injective on literals

**Claim.** `Literal.flipNeg (n := n)` is injective as a function
`Literal n → Literal n`.

**Proof.** Structural, from the fact that `flipNeg` keeps `var` and applies the
involution `!` to `neg`.

1. `intro l₁ l₂ h` and `cases l₁; cases l₂` expose both literals as explicit
   `⟨var, neg⟩` pairs.
2. `simp [Literal.flipNeg] at h` turns the hypothesis into equality of the
   variables together with `!neg₁ = !neg₂`, which `simp` reduces to
   `neg₁ = neg₂`.
3. `Literal.mk.injEq .. ▸ h` repackages the componentwise equalities into
   `l₁ = l₂`.

**Used in.** `cnfToDualDNF_nodup`: a clause with no repeated literals stays
duplicate-free after every literal is negated (`List.Nodup.map`).
