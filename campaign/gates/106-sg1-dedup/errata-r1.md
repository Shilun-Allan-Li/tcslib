# Erratum to the immutable gate106 round-one pack

SingleTape's retired dgSpan_add has **six consumer declarations and twelve composition calls**:
dg_init3, dg_collect1, dg_turn_with_growth2, dg_end_with_growth2, dg_step3, dg_simulate1.
The former seven counted matching source lines, including the helper declaration. All12
calls were repointed. The issued166-section bundle and its original pack are preserved.
