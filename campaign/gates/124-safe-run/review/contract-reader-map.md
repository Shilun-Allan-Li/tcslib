# Exact SafeRun reader contracts

All existing formal headers/docstrings are literal in the complete owner and
source-reversal map. This explanation adds no statement or implementation.

| Source scope | Preserved meaning | Exact existing reader and adapter |
|---|---|---|
| private `safeRun_iff_segment` | The own SafeRun run equality and strict-before-end state avoidance are equivalent to a Segment with forbidden set `{some avoid}` and head-position predicate `True`. | Own `SafeRun` may unfold. Public `segment_iff` exposes the imported Segment contract; `Set.mem_singleton_iff` identifies membership with equality, and `implies_true`/`and_true` discharge only the trivial invariant. Imported ordinary Segment/run/step definitions stay guarded. |
| public `SafeRun.zero` | `SafeRun H avoid c 0 c`, with no nonavoidance or nonhalting hypothesis. A zero-time strict cut contains no earlier state. | `Segment.zero True.intro`, transported by the single private iff. This imposes no forbidden-state condition at the endpoint. |
| public `SafeRun.cons` | From `H.step c = c₁`, `c.state ≠ some avoid`, and `SafeRun H avoid c₁ t c'`, obtain `SafeRun H avoid c (t+1) c'`. | The private iff converts the tail. Singleton nonmembership follows from exactly the existing `hc`; the head invariant is `True`. Public `Segment.cons` gives time `1+t`, and `Nat.add_comm 1 t` supplies the sole time-order conversion. No nonhalting assumption is introduced. |
| public `SafeRun.trans` | Compose runs ending/starting at the exact same `c₁`, obtaining time `t₁+t₂` and the same forbidden state. | Convert both inputs with the same private iff, call public `Segment.trans`, and convert once back. Both use the identical singleton set/trivial invariant; no endpoint avoidance assumption is added. |

Canonical public statements are in the complete Basic.lean captures at
`segment_iff:432`, `Segment.zero:444`, `Segment.trans:464`, `Segment.cons:539`.
All four complete proof scopes, including the private bridge before any public
caller, are inside the sealing context. The own SafeRun definition is allowed;
imported theorem proof values are citation boundaries. Seven guards, fourteen
paired controls and selected AX/type metadata give the stated bounded evidence.
This is no global absence, full-environment metadata or debt-retirement claim.
