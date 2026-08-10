<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: PauliNZ.toBasis_ne_I -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The non-identity Paulis never embed to the identity

**Claim.** For every `a : PauliNZ`, `a.toBasis ≠ PauliBasis.I`; that is, the
inclusion `PauliNZ.toBasis` of `{X, Y, Z}` into `PauliBasis = {I, X, Y, Z}`
misses the identity element.

**Proof.** Immediate from a three-way case split:
`intro a; cases a <;> simp [PauliNZ.toBasis]`. Each branch reduces to a
disequality between distinct constructors of `PauliBasis`, which `simp` closes
using the derived `DecidableEq` instance.

**Used in.** `support_mkWithSupport`, where it is the simp lemma that forces
`mkWithSupport S f` to be non-identity at every `i ∈ S` — the direction of
`support (mkWithSupport S f) = S` that is not true by definition. Deliberately
granular: it exists only so that one `simp` call there goes through.
