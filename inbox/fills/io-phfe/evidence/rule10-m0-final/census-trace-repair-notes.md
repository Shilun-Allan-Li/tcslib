The native collectAxioms traversal includes inductive constructors. The initial trace
helper followed type/value references only, so PGTargets had no reported path despite a
valid collectAxioms result. The corrected helper also follows inductInfo.ctors.
Complete native chunks remain identifiable by their PHFE_CENSUS_CHUNK marker.
After the original pass ends, every incomplete chunk will be rerun with the corrected
helper; overlapping type/axiom records must agree, and the merged name set must equal
all2225 native ROOT names. Original failures remain preserved and are not called clean runs.
No library source or statement changed.
