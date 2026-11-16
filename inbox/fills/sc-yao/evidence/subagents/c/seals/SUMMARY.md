12/12 whole-file seals pass; 4/4 unsealed controls pass; 4/4 sealed controls fail exactly once.
A/B are eval-notation/eval-sealed; strict/coe differ only in projection-coercion exemption.
No failing library declarations.
Lengths_A_strict.lean: exit=0 errors=0 expected=0
Lengths_A_coe.lean: exit=0 errors=0 expected=0
Lengths_B_strict.lean: exit=0 errors=0 expected=0
Lengths_B_coe.lean: exit=0 errors=0 expected=0
OTInputs_A_strict.lean: exit=0 errors=0 expected=0
OTInputs_A_coe.lean: exit=0 errors=0 expected=0
OTInputs_B_strict.lean: exit=0 errors=0 expected=0
OTInputs_B_coe.lean: exit=0 errors=0 expected=0
TwoMoveViews_A_strict.lean: exit=0 errors=0 expected=0
TwoMoveViews_A_coe.lean: exit=0 errors=0 expected=0
TwoMoveViews_B_strict.lean: exit=0 errors=0 expected=0
TwoMoveViews_B_coe.lean: exit=0 errors=0 expected=0
Control_A_strict_unsealed.lean: exit=0 errors=0 expected=0
Control_A_strict_sealed.lean: exit=1 errors=1 expected=1
  evidence/subagents/c/seals/controls/Control_A_strict_sealed.lean:48:2: error: Tactic `rfl` failed: The left-hand side
Control_A_coe_unsealed.lean: exit=0 errors=0 expected=0
Control_A_coe_sealed.lean: exit=1 errors=1 expected=1
  evidence/subagents/c/seals/controls/Control_A_coe_sealed.lean:48:2: error: Tactic `rfl` failed: The left-hand side
Control_B_strict_unsealed.lean: exit=0 errors=0 expected=0
Control_B_strict_sealed.lean: exit=1 errors=1 expected=1
  evidence/subagents/c/seals/controls/Control_B_strict_sealed.lean:48:2: error: Tactic `rfl` failed: The left-hand side
Control_B_coe_unsealed.lean: exit=0 errors=0 expected=0
Control_B_coe_sealed.lean: exit=1 errors=1 expected=1
  evidence/subagents/c/seals/controls/Control_B_coe_sealed.lean:48:2: error: Tactic `rfl` failed: The left-hand side
