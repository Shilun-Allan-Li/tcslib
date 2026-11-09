# Dyadic arithmetic statement report

Frozen Lean/root: `dbacd91218c19f0df106d316ce4ff0e22b869e66`.
The new mathematical module is committed separately at
`11ec6c1c19deef1bcbd5d4ed2c30207e8abd12a7`; the Encoding export is the next
commit. The branch targets `cryptography/lwe-sis-constructions`, carrying audited
dependencies #236/#237/#238 without merging or pushing the central branch.

There are 18 declarations: three definitions and fifteen theorems. Three complete
defining equations are proved by `rfl`; twelve semantic, length, residue-ring and
FP obligations remain admitted with sketches. Addition/multiplication retain low
bits. Subtraction normalizes the right operand and adds the modulus before natural
subtraction, covering overlong operands without a fit premise. The modulus word
has polynomial bit length. Templates are arbitrary; zero width and malformed
pairs have the documented total default behavior.

| Check | Result |
|---|---|
| Fresh serial sweep | 94 modules, 212.139 seconds, zero errors |
| New / inherited admission warnings | 12 / 17 |
| Fresh probe | 30.383 seconds, zero errors |
| Earlier constants | All 284 retain identity and exact axiom sets |
| Total owned constants | 302; exactly twelve disclosed `sorryAx` constants |
| New compiler auxiliaries | Zero |
| Backing public contracts | Sixteen, all only standard axioms |
| Scoped style | 0 FAIL / 2 unchanged WARN over twenty files |
| Finite model | 630,831 scalar comparisons; not parser/Lean/complexity verification |
| Existing-source overlap | One Encoding facade import/contents entry |

All 100 other frozen paths match. No new host, copied proved infrastructure,
shared owner API edit, root export, pin change or Mathlib cache root is added.
The native fetch fails DNS; GitHub verifies the unchanged central base. The eight
cached package directories and 93 development objects are cloned from this same
chat's own earlier checkout; the final gate checks every module into a newly
empty owned object tree. Fifteen declared manifest pins stay fixed. Physical
cache/native freshness and isolation remain attestations; no whole-root check is
claimed. Root jobs are serial, no other chat's resources are changed and no PID
is killed. setup.json, cache-setup.json and resource records state exact limits.

Six earlier gates pass. The adapter proof report supplied by user paste is
preserved verbatim, with its separate dispositions and intake checks. Source
validation/ingestion/approved matching, applicable landing checks and later
sampler/schedule/matrix/primitive bridges remain open. No external job, push or
merge is performed by this statement preparation.

**Not yet clear to merge — statement audit and proof fill are pending, alongside
source-policy work, relevant landing checks and user approval.**
