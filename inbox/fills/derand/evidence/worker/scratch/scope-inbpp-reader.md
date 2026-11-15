# Scope request SR-01: a published BPP witness reader

Requested by the external Codex derand r2 worker on 2026-11-15 PST.
Issue base: `01de2d8baed9113e4a099e13c5d50c81e6dbc66f`.

The final route begins by extracting a Boolean verifier and its coin schedule from
`Randomized.InBPP Randomized.polyTimeModel L`. `InBPP` is an ordinary `def` in
`TCSlib/Complexity/Randomized/Classes.lean:288`. There is no direct characterization
or witness extractor at the issue base. Destructuring the hypothesis by its body
would violate Rule 10. The `inBPP_iff_inBPPAt`, `inBPPWith_iff_inBPP`, and
`mem_BPP_PTM_iff` equivalences lead to other foreign definitions and do not expose
the needed witnesses. No change is requested to the definition or any existing
statement/proof.

Request: add exactly the 12-line, attribute-free `Randomized.inBPP_iff` reader in
the accompanying patch, immediately beside `InBPP`, proved by `Iff.rfl` in its
defining file. Its full signature is in the patch. The file's inherited length
already exceeds 1000 lines; the request includes retaining that existing layout
for this one reader. I will record a fifth changed file, run its full seals and
axiom census, and rebuild its consumers in the supplied order if approved.

This is beyond E1–E3, so the issued brief's Scope rule requires Seyoon's answer.
The final-route extraction is paused pending that answer. The base bootstrap and
the already-authorized checkpoint-1 work continue independently.

Answer: PENDING.
