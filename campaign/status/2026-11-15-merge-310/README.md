# #310 merge and snapshot adoption (2026-11-15)

Seyoon merged #310 (Ladner fill 2: `powCap`, the padding parser, the shared `sqStep` round, and the readers `mod_eq` and
`encodeNat_eq`) at `fe8a8520f65a9feaa4c960c11874b68ebf8798db`. Outside `campaign/` it equals the gate 137 round 2 replay's
tree `162b0b2b`, so that replay's output becomes the campaign snapshot (`oleans-cfe8a`, 876 objects, each rehashed on disk
against the replay's map). The previous snapshot `oleans-ca052` is kept as a fallback. See `ADOPTION.json`.
