<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_inc_pointer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter and Pointer Increment

**Claim.** When $r$ is tape $0$ or tape $3$, incrementing the counter on tape $r$ yields the configuration with that counter increased by one, the other displayed counters unchanged, and the tape-$2$ head still at $q$.

**Proof.** Apply the binary counter increment result to tape $r$, starting from the given configuration. The initial configuration is safe by the bound on $q$ and the standard safety bound for the binary encodings; the counter increment is permitted by the hypothesis on its value. The resulting path ends with the selected tape containing the binary encoding of its value plus one and its head at zero, while the other configuration data are retained (`Complexity.LogProg.access_inc`). Finally split according to the two possibilities for $r$. Since $r=0$ or $r=3$, the updated encoding is exactly the corresponding entry of $(i,0,k,p)$ with that entry increased by one; the other three entries agree. Tape $2$'s head remains at $q$, as it was unchanged by the increment on tape $0$ or $3$, giving the stated target configuration.

**Key facts.** `Complexity.LogProg.accessCfg_safe`, `Complexity.LogProg.access_inc`.
