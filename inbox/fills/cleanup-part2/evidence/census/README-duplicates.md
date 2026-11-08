The census tables of the final head live in `final/` (probe `FinalCensus3` at `03ead73ab`).
Two earlier runs produced byte-identical tables and are recorded by hash only (not duplicated
in the payload): `final-run1` (probe `FinalCensus` at `ea37eb57c`, before the C3 collector's
root enumeration was widened) and `final-at-ea37eb57c` (probe `FinalCensus2` at `ea37eb57c`).
`final.SHA256SUMS`, `final-run1.SHA256SUMS` and `final-at-ea37eb57c.SHA256SUMS` list the same
four SHA-256 values (names, axioms, c3, closure).
