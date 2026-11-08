<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance computation for the access machine

**Claim.** For each mode and Boolean word $y$, some natural numbers $k,p$ give a finite safe path from the initial scan configuration on $y$ to a halting configuration outputting the indicator of membership in the access language.

**Proof.** First identify the initial configuration with the access-machine scan configuration whose four registers are zero. If $y$ has the encoded form $\langle z,\mathrm{bits}(r)\rangle$, the valid-input computation lemma supplies a safe run ending with output `accessValue mode z r` (`access_valid`). On such an encoded input, the membership indicator of the access language is exactly this value: the indicator on an encoded pair agrees with deciding the defining predicate (`indicator_indexLang_pairEncode`), and the indicator itself is the Boolean decision of membership (`indicator_eq_decide`). This identifies the endpoint required by the claim.

If $y$ is not an encoded pair, the scan check cannot succeed: whenever the check returns a value, it certifies that $y$ is such an encoding (`accessCheck_some`). Hence the scan ends in the rejecting exit state. The indicator is false as well, since membership would provide an encoded-pair witness. The scan-run lemma reaches that rejecting state (`access_scan_run`), and the answer routine converts it to a halting configuration outputting false (`access_answer`). Taking $k=p=0$ in this case and composing the paths proves the result.

**Key facts.** `Complexity.LogProg.access_valid`, `Complexity.LogProg.indicator_eq_decide`, `Complexity.indicator_indexLang_pairEncode`, `Complexity.LogProg.accessCheck_some`, `Complexity.LogProg.access_scan_run`, `Complexity.LogProg.access_answer`.
