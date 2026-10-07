<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: encode_go_acc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The encoder's accumulator is only ever prepended to

**Claim.** For all `f : DNF n`, `w`, `fuel`, `path`, `ρ₀ σ : Restriction n` and
`acc : List (ℕ × Bool)`,

```
razborovEncode.go f w fuel path ρ₀ σ acc
  = let r := razborovEncode.go f w fuel path ρ₀ σ []; (r.1, acc ++ r.2)
```

so the starting accumulator does not influence the γ-component at all, and
contributes to the aux output only as a literal prefix.

**Proof.** Induction on `fuel`, generalizing `path`, `ρ₀`, `σ`, `acc`.

1. `fuel = 0`: `cases path <;> simp [razborovEncode.go]` — both base equations
   return `(σ, acc)`, and `acc = acc ++ []`.
2. `fuel + 1`, `path = []`: same base equation, `simp [razborovEncode.go]`.
3. `fuel + 1`, `path = step :: rest`: `simp only [razborovEncode.go]`, then
   `split` on `f.find? (fun t => decide (¬Term.killedBy t ρ₀))` (`none` branch
   returns `(σ, acc)`, closed by `simp`) and `split` again on the filtered
   free-literal list (`[]` branch likewise).
4. In the remaining branch the loop recurses with accumulator
   `acc ++ pcl.2.2.2 ++ [(w, false)]`. Apply the induction hypothesis twice —
   `rw [ih, ih (acc := _ ++ _)]` — once for the actual call and once for the
   `acc = []` call, then `simp [List.append_assoc]` reassociates the two
   prefixes.

**Used in.** `encode_go_fst_acc`, `encode_go_snd_sigma_indep`, and the aux-block
bookkeeping of `go_roundtrip_gen` in `Switching/RoundTrip.lean`.
