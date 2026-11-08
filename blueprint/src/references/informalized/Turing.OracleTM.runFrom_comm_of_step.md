<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_comm_of_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs Preserve Step Correspondence

**Claim.** If applying one step in the target machine to $f(c)$ agrees with applying $f$ after one step in the source machine, then the same correspondence holds after any number of steps.

**Proof.** The hypothesis says that $f$ intertwines the two one-step updates, with the equality oriented from the target update back to the image of the source update. Iterating this relation gives the corresponding equality for every finite iterate: the target machine's $n$-step iterate at $f(c)$ equals $f$ applied to the source machine's $n$-step iterate at $c$. Taking the symmetric form of that iterate identity yields the claimed equality.
