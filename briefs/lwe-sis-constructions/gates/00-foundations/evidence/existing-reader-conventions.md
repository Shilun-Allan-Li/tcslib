# Existing assumption-reader naming

Read-only excerpts from the frozen source; these files are unchanged by this branch.

## TCSlib/Cryptography/Candidates/RSA.lean:114

Frozen source: 4364d0e0fe9accd649b6acb4751e8684aa93ad1e; whole-file SHA-256: 2d0b9e00ab0f21686f64429686405eb3e7bc249c46ecaa087f04e50236e17f7f

```lean
roots modulo a random `N = pq` with negligible probability.

**Deviation:** "`Pr[…] < ε(n)` for a negligible `ε`" is "`Pr[…]` is negligible"; see the
module docstring for the distribution and the input/output conventions. -/
def RSAAssumption : Prop := ∀ A : NUPPT, Negligible fun n => rsaProb A n

/-- Unfolding: the RSA assumption is the negligibility of every `rsaProb`. -/
theorem rsaAssumption_iff : RSAAssumption ↔ ∀ A : NUPPT, Negligible fun n => rsaProb A n :=
  Iff.rfl

/-- The RSA probability is nonnegative. -/
```

## TCSlib/Cryptography/Candidates/ElGamal.lean:402

Frozen source: 4364d0e0fe9accd649b6acb4751e8684aa93ad1e; whole-file SHA-256: 6d90bbb78b60e644eb4fe63c10a9f7ca35a4d30019a54bc558995b773e52df31

```lean
the exponents are read from `n · n`-bit seed blocks by rejection, within `2^{-n}` of uniform
in `Z_q` (`ddhExpo`, D10; run-3 audit P8-1 — equivalent to the ideal-exponent form up to a
negligible statistical term); the tuple is a bit string of `15n + 14` bits; the
distinguisher receives `1^n` (D5). -/
def DDHAssumption (G : SafePrimeGen) : Prop := (ddhReal G).Indist (ddhRandom G)

/-- Unfolding: the DDH assumption is the indistinguishability of `ddhReal G` and
`ddhRandom G`. -/
theorem ddhAssumption_iff (G : SafePrimeGen) :
    DDHAssumption G ↔ (ddhReal G).Indist (ddhRandom G) := Iff.rfl

/-! ## Public-key schemes with a key-dependent message space -/

```
