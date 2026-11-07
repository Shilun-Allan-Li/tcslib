# Implications layer — campaign work item I1

**Authorized by Seyoon Ragavan, 2026-11-07 PST. Drafting, not issued for an external job.**

Collect, by cryptographic primitive, the end results of the library's construction chains:
an explicit set of hardness assumptions jointly implies existence of a fundamental primitive
with a precise security notion. A first-class entry is a final implication, not every step of
its construction chain (user clarification, 2026-11-07 PST).
Keep the proofs short applications of the existing results. The user requested this after
tracing RSA to public-key encryption and observing the uncomposed encoding bridge.

## Proposed layout

- `TCSlib/Cryptography/Implications.lean`: facade, exported from `TCSlib.lean`.
- `Implications/PublicKey.lean`: first pilot. The user-selected catalog endpoints are multi-message
  IND-CPA PKE and multi-message IND-CCA2 PKE (2026-11-07 PST). CCA1 is a documented intermediate.
  Existing single-bit, hard-core-TDP, bitwise and security-lifting lemmas stay supporting APIs.
- Later coherent modules for pseudorandomness/private-key encryption, authentication,
  commitments/zero knowledge, and oblivious transfer. Split by primitive as contents grow;
  this is an output-facing composition layer, above candidate and construction modules.

Dependencies point toward Implications. Definitions, candidate modules and reduction modules
never import it. The short proofs cite their public APIs and preserve every cost, domain,
length and auxiliary hardness hypothesis. Thin compositions through existing APIs need no new host. Precise multi-message target
predicates and model conversions still require design where the existing APIs do not express
the selected guarantee.

## Admission to the catalog

A result belongs here when it connects a useful, explicitly stated assumption set to a
fundamental primitive. Include all computational infrastructure, domain, length, correctness
and auxiliary hardness premises in its header. Several independent assumption sets may have
theorems with the same endpoint. Intermediate constructions and automatic weaker guarantees
are indexed through links, rather than promoted into parallel catalog entries.

The PKE target must support a meaningful message space (for example n-bit messages with a
proved extension), so an existential cannot be witnessed by an empty-message-only scheme.
Multi-message security is part of the intended endpoint, with the exact experiment stated;
it is not a separate primitive category. No source-level single-message claim is silently
relabelled as an adaptive multi-challenge game.

## Contents and status

`public-key-draft.md` gives proposed statements, proof terms, existing source locations and
blockers. `normalization-design.md` records a constant-shift route to the concrete RSA/Rabin
width bridge, with the missing transports explicit and no checked-proof claim. `inventory-draft.md` surveys 13 primitive families and their exact endpoints, retained premises, admissions and missing bridges. The first source survey is against
campaign records/source `f3c7958506bd258863a0adf93e4cc0aa3183336e`; Gate 06-only declarations are identified separately and
are not yet landed or externally statement-gated.

A result index records assumption, precise conclusion, implementation theorem, hypotheses,
source reference, gate/fill status and remaining bridge. A source `sorry` count of zero in a
wrapper is insufficient: inspect its full axiom dependency set and the status of its callees.

Do not publish RSA/Rabin existence wrappers with the current impossible `henc` premise. Keep
those chains as blocked index rows until their real normalization/padding bridge is available.
Likewise, ElGamal's GroupPKScheme security is not silently a theorem about the other PKE types.

## Execution

1. Complete and review this draft inventory while Gate 06 integration/checking continues.
2. Use the selected public-key endpoints and index the already-proved generic
   public-key chain as supporting material. Draft assumption-set-to-endpoint statements;
   add only useful missing final compositions on an isolated PR branch;
   check headers, source fidelity, axioms, seals and exports. The user approves/merges Lean.
3. Add the exact CPA wrappers once their Gate 06 dependencies are gated and filled. Keep
   declared proof-dependency status visible in the index until then.
4. Commission substantive missing bridges separately: design/register public contracts and
   gate statements before fills. Ask Codex or Claude before preparing any external job.
5. Extend the same format to the other primitive families, preserving one-time/many-message,
   computational/statistical, uniform/non-uniform and model distinctions.

The thin composition work is maintainer work; no new external fill is prepared or dispatched
by this draft. It does not delay the already-dispatched S2 or waive its order before cleanup.

**Not yet clear to merge — contents are a draft; no Implications Lean PR exists yet.**
