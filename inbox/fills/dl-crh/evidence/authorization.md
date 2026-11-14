# Scoped freeze exception (user, 2026-11-13 America/Los_Angeles)

User instruction, verbatim:

> You may add expGenFun_eq and expSampleRaw_eq in TCSlib/Cryptography/Candidates/DiscreteLog.lean as a scoped exception to the freeze. Resume the fill with Rule 10 intact and include those reader changes in the delivery.

The issue base and all other freeze/Rule 10 requirements remain in force.

## Host concurrency override

The user answered the host-serialization question:

> Override; at most 3 Lean processes at a time.

The resumed worker counts active Lean processes before launching a check.

## Coordination-note authorization

The user answered “Send the coordination note” to the request to message the
other Codex fill chats. The authorized note about the shared three-process cap
and reserving one slot for dl-crh was sent to the Lamport, hash-and-sign,
ext-nosrc, and Ladner fill-route chats. No external person was messaged.
