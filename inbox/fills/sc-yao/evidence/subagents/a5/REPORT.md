# Generic matched-coordinate re-randomization

## API and result

CoordinateSwap.swap exchanges selected full-table coordinates and independent challenge
coordinates, retaining the unchanged control and every unmatched coordinate on either side.
pick p i = some j iff place p j = some i is the entire matching contract. The construction
is an involution on `(P × (I → V)) × (J → V)`; equiv exposes it as a joint-seed bijection
with public equation readers and generated non-simp projection readers.

acceptProb_swap proves exact acceptance equality for any sampler of the full seed.
acceptProb_fill transports that law to arbitrary finite S/T via seedEquiv and challengeEquiv.
Its remaining premise is exactly the concrete coordinate fill identity. It imposes no
equality, injectivity or distinctness assumption on V: repeated actual key/nonce values are
allowed. Decidable equality is needed only for finite address enumeration I/J. Dropping the
unused challenge coordinate requires its domain nonempty.

The pure swap/bijection has no finiteness or nonemptiness hypothesis. Unused padded slots
are retained on both applications. The probability law needs finite spaces only for the
existing acceptance experiments; it never re-proves their counting identity.

P can contain raw XOR masks and all unused padding. Selectors may compose through the
induced permutation map, which need not be injective or uniformly distributed over all
permutations. This avoids assuming that actual Yao tapes sample every row permutation.

## Ownership and reuse

b owns concrete pick/place, their inverse law, seed coordinate equivalences, SelectedSeed.fill
and the cryptographic sampler identity. The exact interface was coordinated before coding.
b/c are coordinating the actual tape split into unchanged coordinates and value tables.
See SEARCH.md for existing single-coordinate and probability relatives; none was copied.

The generic algebraic helper belongs under the brief's permitted helper tree in this fill.
After integration it could be promoted to a common probability/sampling helper module in a
shared-file window. No frozen file or lead/b/c-owned source was edited, and no new host or
PT machine is introduced.

## Normal iterations

CoordinateSwap05 is normal PASS, zero errors/warnings/admissions; final style has zero
findings. All raw failed sources and logs remain. Function-space enumeration initially
needed explicit decidable equality on address types. The transported fill proof also needed
the public Prod.map_apply' equation after Equiv.prodCongr_apply. Those were source-directed
repairs; no timeout or resource termination occurred.

## Final audit

Whole-file A/B by strict/coe seals, controls, and the complete fifteen-owned-module stored
constant trace are under probe-runs/audit-01. Results will be appended when complete.

Final audit complete: four of four CoordinateSwap seal variants pass, with maxErrors=0
and the full imported TCSlib closure sealed. Four positive controls pass; each of four
deliberately sealed negative controls has exactly one error. All sixty final variants across
fifteen owned modules pass (the prior simulator documentation-only token comparison remains
explicit in a4). The complete fifteen-module trace covers 296 stored constants, including
private/generated declarations: no transitive admission closure; only standard axioms.
No own process or batch remains active. No child commits or delivery were performed.
