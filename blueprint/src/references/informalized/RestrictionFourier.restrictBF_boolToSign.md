<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: restrictBF_boolToSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restriction commutes with the ±1-encoding

**Claim.** For `f : (Fin n → Bool) → Bool` and a restriction `ρ`,

`restrictBF (fun x => boolToSign (f x)) ρ = fun x => boolToSign (restrictFn f ρ x)`.

That is, restricting the real-valued ±1-encoding of a Boolean-valued function
gives the same thing as encoding the restricted Boolean function: the
real-valued restriction operator `restrictBF` and the Boolean-valued one
`restrictFn` agree through `boolToSign`.

**Proof.** Immediate from `rfl`. Both sides unfold to
`fun x => boolToSign (f (ρ.extend x))`, since `restrictBF g ρ = fun x => g (ρ.extend x)`
and `restrictFn f ρ = fun x => f (ρ.extend x)` are definitionally that.

**Used in.** `TCSlib/BooleanAnalysis/LMN/FourierConcentration.lean`, where the
Fourier machinery (stated for `BooleanFunc n = BoolCube n → ℝ`) has to be
applied to a `Bool`-valued function restricted by `ρ`; this lemma is the bridge
in both directions of that argument.
