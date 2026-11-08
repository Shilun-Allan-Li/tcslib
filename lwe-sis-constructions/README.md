# LWE/SIS construction campaign exchange

This namespace belongs to the separate LWE/SIS campaign. It is independent of the
Pass–Shelat and Arora–Barak namespaces. Inputs are read from GitHub; the user
selects and dispatches all external jobs. Return reports in chat unless the user's
specific job assigns another delivery path. Never merge this orphan exchange into code.

The central code integration branch is `cryptography/lwe-sis-constructions`.
Lean changes go through audited PRs approved and merged by the user. PR #236's
foundation statement and representation-proof gates both passed 0/0/0/3; the
reports are preserved at code head `0769cba3e44c56700349f954190fc99d9e622270`.

The construction-core statement and proof gates both passed 0/0/0/3. Their
verbatim reports and separate dispositions are included in the code records.
The next prepared input is `outbox/gates/04-encoding-adapters-r1/README.md`:
source `6eec97be8f54d9990340900a5595dab32fb477f5`, records `82f01285d688c09ddbce370a34f20944ba206fb6`, 14 admitted adapter obligations.
The new draft branch is `cryptography/lwe-sis-adapter-statements`, targeting the
central branch and depending on audited PRs #236/#237. No adapter gate verdict,
reviewer selection or dispatch is claimed. Earlier folders remain historical
and unchanged; source-policy work and user integration remain outstanding.
