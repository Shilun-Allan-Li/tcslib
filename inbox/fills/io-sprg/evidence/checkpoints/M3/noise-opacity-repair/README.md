The c767 intermediate local checks were held from publication after a focused
foreign-lpnNoise opacity probe failed at an implicit coin-type cast.

Internal.lpnNoise_law_cast now publishes that existing scalar law with the exact
cast used by noiseValue. The locality consumer uses it without foreign cast_eq.
The focused V2 and post-cleanup V3 checks pass; these are single-definition diagnostics,
not canonical full-import-closure seals. All earlier failed sources/logs remain.
Eight separately archived proof-only edits remove twelve prior Lean warnings without
changing any existing header, statement prose, import or attribute. New full-owner,
static and335-theorem checks at the repaired head supersede the unpublished v1 checks.
