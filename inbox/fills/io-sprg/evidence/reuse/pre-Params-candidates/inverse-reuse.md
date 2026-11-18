# Exact-power inverse reuse

The preferred candidates are inverse/01 through inverse/04. All are untested.
Use TCSlib.Cryptography.Asymptotic.UniversalPadding.Parameter (now imported by root),
not a duplicate Nat.findGreatest proof. nu_eq rewrites the existing Params readers
without unfolding another TCSlib definition. nu_pow_le gives the upper power bound;
Nat.pow_le_pow_iff_left with a nonzero exponent gives the upper base bound; le_nu
at the exact input power gives the reverse inequality. For N, first normalize
(κ^E)^D to κ^(E*D), using the public Nat.pow_mul equation in the reverse direction.
D_pos and one_le_E give E*D>=1. nu_le handles both arbitrary-input upper bounds
without any positivity requirement and works at zero. No new generic lemma or
search implementation is needed. Exact source locations and prerequisites are
listed in README.md and reuse-searches.json.
