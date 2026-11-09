# Checked short-query numerical clock envelope

Scratch route probe on the verified post-#249 Lean tree `770a4488e1bb770a3b7c9c878327fc2d468dd7f2`,
using the existing import context. The complete proof elaborated, with
only the standard axioms. Source and output are in checked/; earlier
failed scratch attempts are preserved separately. This adds no Lean
declaration to the campaign.

Let a be floor(log₂ n) and k be floor(log₂ a). For a short word of
length m ≤ a and index i < k, (k+1)i ≤ k(k+1) ≤ 2^(k+1) ≤ 2a.
Since a < 2^(k+1), m^i ≤ 2^(2a) ≤ n²; hence i·m^i ≤ n³.
The existing bit-length bound gives bits(i).length ≤ n. The exact
simulator polynomial expression is therefore bounded by
(d·4^d)·(n+1)^(3d). The proof handles all natural d, including d=0.

This discharges the numerical envelope leaf recorded in LADNER-design.
The explicit setup clock and FP simulator-input preparation, sharp SAT
verifier interface, memo transition/readout and orbit size, and remaining
mathematical targets are still separate. No fill has been dispatched.
