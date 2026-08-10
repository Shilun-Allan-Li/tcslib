<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: restrictFn_composeRestr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restricting by a composed restriction is restricting twice

**Claim.** For `f : (Fin n → Bool) → Bool` and restrictions `ρ₁ ρ₂ : Restriction n`,
`restrictFn f (composeRestr ρ₁ ρ₂) = restrictFn (restrictFn f ρ₁) ρ₂` — an equality
of functions, not merely a pointwise one.

**Proof.** Immediate from `unfold restrictFn composeRestr Restriction.extend; aesop`.
All three definitions are pointwise: `restrictFn f ρ x = f (ρ.extend x)`,
`(composeRestr ρ₁ ρ₂) i = (ρ₁ i).orElse (fun _ => ρ₂ i)`, and
`ρ.extend x i = (ρ i).getD (x i)`. After unfolding, both sides send `x` to `f`
applied to the assignment that takes `ρ₁ i` where `ρ₁` fixes `i` and `ρ₂.extend x i`
otherwise; `aesop` closes the remaining `Option` case split.

**Remark.** This is a `private` local copy: an identical public
`theorem restrictFn_composeRestr` lives in
`TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean` (same namespace, same statement,
essentially the same proof). This module does not import that file, hence the
duplication.

**Used in.** `compress_and_switch` (same file), twice — to rewrite the two-stage
restriction `composeRestr ρ₁ ρ₂` into the form the switching lemmas
`switching_bernoulli_dtDepth_cnf_general` / `..._dnf_general` expect.
