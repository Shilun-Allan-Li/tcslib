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

## Facade lint exception

The required lint reported exactly six new ancestor-facade direct-import
diagnostics, although all six helpers are exported through the owned facade.
The user replied verbatim: “Acknowledge exactly six lint false positives”.
Details and the exact scope are retained in `facade-lint-exception.md`.
The frozen `Hashing.lean` is unchanged; raw lint counts are reported honestly.

## Incoming Lamport coordination note and gate hardening

The Lamport worker sent an authorized coordination note reporting bare `lean`
compiler names as well as full toolchain paths. The current host sample showed
two Lean compilers and both count methods agreed on two. The launch gate was
nevertheless hardened to count the final whitespace-separated `comm` field,
accepting both full paths and bare `lean` robustly. Its prior bytes are retained
as `evidence/tools/wait_lean_slot-pre-trim.sh`; replacement was atomic so active
shells retain their original complete source bytes. The cap remains three and
this worker's checks remain serial. No other chat was messaged in response.
