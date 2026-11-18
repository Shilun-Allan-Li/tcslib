# Independent static M3 template audit

PASS for coverage and mathematical abstraction fidelity, not a Lean/proof pass.
No source/import change, Lean, Git, cache or agent was used.

The probe index has23 entries:12 new helper cores +5 original non-Load cores +5
original Load goals +1 public bridge control. names.txt has the22 non-controls;
control-names.txt has only cond2_hunif_control. Every indexed template exists,
its import list exactly matches the index, and every template has one body marker.
No template was missing, so none was created or modified. No StructuredSeed owner
is imported by any template; candidate/self theorem hits are excluded.

core-to-source-map.tsv gives every exact source/helper identity and the preceding
public-reader/helper conclusions abstracted by its goal. The detailed reviewed
SHA-256 bindings are in summary.json.

No exact self-goal premise or vacuous core was found. In particular:

- cond1_all_fixed_index assumes the earlier tuple event bound and adds only an
  independent Boolean seed; it does not assume its product conclusion.
- cond1_all_joint averages the actual possibly nonuniform index computation. Its
  section-bound premise is the earlier fixed-index theorem.
- cond2 keeps smallness inside the event and samples independent buckets LAST;
  S ignores bucket labels, not the actual generator draw/matrix/noise coordinates.
- claim42 assumes the earlier decomposition/component estimates and the separate
  prefactor estimate. Both eventual thresholds precede every pp. It does not
  assume the final error bound. PP may be abstract/empty in a generic family, but
  no existence is claimed and actual specialization is PrimeParam; this does not
  make the real prime-uniform conclusion vacuous.
- badSet expands actual variable sets and the scalar selector/integer-lift noise,
  retains the full uniform coordinate vector, and assumes only the real locality
  cardinality bound. It does not hide the sought expectation bound as a premise.
- κ=0 is retained where original goals require it; later tail helpers explicitly
  take κ≥12, as their actual statements do. Original strict thresholds are kept.

The actual-law, cast and type transport surrounding some cores are NOT searched
by a smaller arithmetic core. They remain explicit candidate obligations. The
additional six templates under M3Claim42Bodies/overlap are useful supplemental
searches for coordinate marginals, actual joint pushforward transport and failure
partition logic; they do not replace or inflate the22 regular M3 source goals.

Harness qualifications:

The templates themselves use maxHeartbeats0, but current evidence/tools/overlap_step.py
replaces that with100000 for saved diagnostic runs. Invoke the bounded root driver;
do not run a materialized template unbounded outside it. No new unknown-scope
problem was found statically: every template that needs sums/products imports a
public owner providing BigOperators notation; no unconditional unused scope line
was added. Actual elaboration remains the root's responsibility.

The cond2_hunif_control goal is the exact existing Type0 sequential pair probability
bridge. A hit must be reused. It is a control, not a thirteenth new helper. The
new Load performance lesson requires explicit sample types and both lambda binders
at uprob_exists_le/uprob_mono calls; original proof candidates can still need that
engineering repair even when their search cores are faithful.
