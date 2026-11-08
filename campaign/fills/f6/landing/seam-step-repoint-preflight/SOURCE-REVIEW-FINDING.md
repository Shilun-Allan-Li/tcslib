# Additional exact public-contract re-point

The resumed full read of all18 new private helpers and the target found an exact public API
reconstruction missed by the original bounded delivery review: Hierarchy f6_seam (f72 source
lines104–121) has exactly the hypotheses and three-part conclusion already packaged by
Turing.seamCompTM_step (Build/InterpreterStartup lines64–83). Rename A/B/exit₁/entry₂/exit₂,
c₂ to M₁/M₂/exit/entry/q₂,c₃ respectively; the premise and conclusion are otherwise the same.
Its tuple separately invokes seamCompTM_run_ofCfg, the mapState state equation and
seamCompTM_firstReturn_ofCfg. The public theorem already packages those same steps.

The theorem is already imported along Hierarchy→SelfUniversal→CodeSimulator→InterpreterStartup.
The exact replacement is `by exact seamCompTM_step M₁ exit M₂ entry q₂ h₁ hexit hcut h₂ hq hcut₂`.
Standing WORKFLOW§3 requires this mechanical re-point in the same PR: no statement, import,
public declaration or design decision changes. The two full preflights pass. This finding is
additional to the previously corrected visited-set monotonicity reconstruction. The original
review is preserved verbatim; its earlier no-extra-repoint conclusion is superseded here.

E1 remains the permitted consumer application of embedEmitCfg_eq, and E3 remains the bounded
one-step stationary-action library-call idiom. Neither disposition excuses this separately
published exact combined seam contract. No general duplication exemption, new debt acceptance,
or global absence claim follows. All inherited screen clusters still need explicit disclosure.
