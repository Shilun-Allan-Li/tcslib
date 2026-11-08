<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Pairing

**Claim.** If $f$ and $g$ are polynomial-time computable, then the function sending $x$ to the pair encoding of $f(x)$ and $g(x)$ is polynomial-time computable.

**Proof.** First, polynomial-time pairing with the input shows that $x\mapsto\operatorname{pairEncode}(f(x),x)$ is polynomial-time computable (`sat_pt_pair_input`). Next, the polynomial-time map on encoded pairs that leaves the first component unchanged and applies $g$ to the second (`sat_pt_mapSnd`) can be composed with this function, using closure of polynomial-time computability under composition (`PolyTimeComputable.comp`). On an input of the form $\operatorname{pairEncode}(f(x),x)$, decoding recovers exactly $(f(x),x)$ (`pairDecode_pairEncode`), so the composed map returns $\operatorname{pairEncode}(f(x),g(x))$.

**Key facts.** `Complexity.sat_pt_pair_input`, `Complexity.sat_pt_mapSnd`, `Complexity.PolyTimeComputable.comp`, `Turing.pairDecode_pairEncode`.
