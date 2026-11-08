# Binary representation adapter statements

Full worktree baseline: `ff8345b1d2ac2f605d81cdf6c23216aadb918abb`.
Mathematical module commit: `f22f0a1404548cccd33ea0feebc2c1c640d0e814`.
Separate facade export / Lean-root freeze:
`6eec97be8f54d9990340900a5595dab32fb477f5`.
Draft branch: `cryptography/lwe-sis-adapter-statements`.
Central PR target: `cryptography/lwe-sis-constructions`; audited dependencies #236/#237.

## Scope

Candidates' encodings are fixed-width MSB words; the reusable binary machines
consume normalized little-endian words. The new owned module gives three total
functions and their semantic, length, round-trip and polynomial-time contracts.
All nontrivial contracts remain admitted for statement review. The only proved
theorems are the three full defining equations, each by rfl.

| Function | Exact behavior | Admitted obligations |
|---|---|---:|
| `toLE` | Reverse an MSB word, then normalize it with `Nat.bits` and the existing LE reader | 4 |
| `normalizeWidthPoly` | Prepend zeros to the payload and drop its original length, retaining exactly the low polynomially many bits | 4 |
| `fromLEPoly` | Reverse a paired LE payload, preserve its parameter template, then normalize its MSB width | 6 |
| **Total** | **3 definitions, 17 theorems, 20 source declarations** | **14** |

Each definition has a complete non-simp `_eq` reader. Every admitted theorem
has a prose statement and adjacent sketch naming its public reuse route. These
are technical repository adapters: PS10's representation convention and AB09's
machine context are cited as context, not as sources of these exact endian or
polynomial-width interfaces.

Templates may contain arbitrary bits; only their lengths matter. Width zero,
empty/all-zero words, leading zeros and overlong operands are covered. Invalid
paired inputs are interpreted through the total projections; this is not a new
rejection parser. Numeric normalization retains the low bits, unlike a prefix
padder. Each efficiency theorem fixes its `PolyExpr` before choosing a machine;
no runtime encoding of arbitrary polynomials is claimed.

The existing zero generator, append/pair combinators, polynomial drop, reversal
and normalization machines suffice. No new host, transition table, copied
proved infrastructure or handwritten helper is added. One internal agent
supplied read-only design/API research; root alone edited and checked the code.
The endorsed shared probability-reader proposal remains unapplied.

## Verification

* Fresh serial 93-module sweep: 181.289 seconds, zero errors, 14 new and the same
  17 inherited admission warnings. The final own tree
  `.lake/adapter-final-2-oleans` was new. No root build fallback or other chat's
  objects were used. This is not a whole `TCSlib.lean` build.
* Source census: 3 definitions, 17 theorems, 14 admissions. Three complete rfl
  equations are the full skeleton-time proof surface. No instances, simp
  attributes, new hardness assumptions or unsafe declarations were added.
* Environment census: 283 owned constants = 263 unchanged audited constants +
  20 new source declarations. Exactly the 14 admitted statements use sorryAx.
  No new compiler auxiliary or unexplained public name is present.
* The old 263 names retain their module, kind, visibility and exact axiom sets.
  Nine named public machine contracts additionally have only standard axioms;
  see `backing-contract-axioms.json`. Thus their filled bodies were checked for
  actual axiom dependencies, not merely counted as source without admissions.
* All 99 other frozen source/policy/pin files match the full audited dependency
  baseline. The new source and one facade edit are the only Lean changes.
  The 101-file freeze and native source hashes match the final source commit.
* Scoped style: 0 FAIL / 2 unchanged acronym WARN over 19 mathematical files.

The first bootstrap attempt failed at the new file because `Turing` had not
been opened for `pairEncode`. Its raw logs and exact pre-repair source remain
under `evidence/iterations/`. Adding the namespace open fixed elaboration.
The separate full fresh successful sweep supplies the gate evidence; no failed
run is counted as a pass. No nontrivial target proof was filled.

## Package and resource provenance

The checkout's packages are isolated APFS clones of this chat's own pinned
archive setup, with no copied TCSlib objects. All eight declared revisions match
the unchanged manifest and earlier archive attestation. Archived sources have
no package Git metadata, so this is not a fresh per-package Git verification.

Only `Mathlib.Computability.Language` was missing. The pinned official cache
hasher computed its selected dependency closure: 721 modules, with all 720
previously selected keys matching the earlier inventory. Exactly one archive,
`2c4aa27121d39fbc.ltar`, was downloaded from the official Azure endpoint and
unpacked with one thread into this checkout alone. Its SHA-256 is
`b1660139c35e2a9df0c1b49e04eb6d6c9eb63f488d275a3cc6a20289ea124f6b`.
No unfiltered cache get, lake build or package source/pin change occurred.

The archive's build comment names `mathlib4@a85b3ecdb6ccf6112332276f5e243a2bf60d615f`.
Selection uses the source/dependency cache key computed at the pinned
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, allowing reuse of an unchanged
artifact across build commits. The comment is disclosed; it was not used to
switch revisions. Cache-source/content isolation and native freshness remain
maintainer attestations. The hash tool reuses only this chat's own three compiled
Cache modules; its `#eval` driver is records/tooling, not library code.

Disk and memory were checked before setup. Process inspection remains sandbox
denied; the approved budget permits root's serial native/cache work while the
internal agent stays read-only. Own PIDs were recorded; no process was killed.
The failed Git fetch is retained as a DNS limitation. The central tracking pin
matches GitHub metadata; no successful shell fetch is claimed.

## Scope limits and routing

All four earlier scoped gates pass. Their reports remain verbatim, including
the construction-core proof report supplied as a user paste. N01 source
validation/ingestion/matching remains open. N02 retains inherited admissions,
scoped native evidence, physical-isolation limits and applicable landing checks.
N03's actual-law samplers, schedules, scalar/matrix adapters, uniform negligible
bounds, raw collision output and final primitive bridges remain open.

This new statement gate does not prove the 14 adapter obligations, an efficient
Regev/SIS primitive, PKE, PRG or CCA2 construction. Shared owner APIs and the
source registry remain untouched. The only shared-file overlap is the Encoding
facade's import and contents entry, isolated in its own commit; reconcile it
before merge if another owner has changed that facade.

The user chooses Codex or Claude for this new external job and dispatches it.
The prepared client command pushes only own draft refs and the dedicated orphan
exchange namespace. It does not merge or push the central/campaign branch.

**Not yet clear to merge — the statement audit and proof fill are pending;
source-policy work, landing checks and user approval remain outstanding.**
