# Correction to the read-only NormalizedStep diagnostic suggestions

Future note after the checkpoint2 closed-evidence manifest. The prior read-only review
was a dated record of inspected sources and plausible implicit-reader hotspots, not a
confirmed root cause. This note corrects the diagnosis in the final evidence without
changing any of those72 sealed bytes.

The lead and a subsequently found that NormalizedStep lacked the direct import of
ZeroKnowledge/Defs.lean declaring NUPPT.simulate. Using with_reducible surfaced that
missing API instead of allowing the unknown/malformed declaration to drive expensive
higher-order definitional-equality work. Adding the import resolved the issue. The lead
will disclose the corrected diagnosis and a's exact interruption/check history in the
root report. The mathematical fixed-point/product route was valid; my earlier read-only
inspection did not identify the missing import.

The generic StatisticalPostprocess helper is independently valid and checked. It is not
evidence that a defect existed in StatClose.map/statClose_iff or that the original theorem
needed weakening. The now-published normalizePhaseMsgs_viewV reader and corrected
NormalizedStep source were copied only after a reported native success and exact source
SHA76766e13e0eff35d107c98505f932dcec17cdf20f89c5f423f7e1d64217884b5;
my own prerequisite check also passed. I did not edit, sample, interrupt, or check a's
foreign tree at any point.
