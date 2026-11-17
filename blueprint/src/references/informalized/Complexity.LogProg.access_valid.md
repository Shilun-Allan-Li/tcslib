<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Access computation returns the indexed bit

**Claim.** For an input encoding $\langle z,\mathrm{bits}(r)\rangle$, if $k\le |z|$ and $k\le r$, the access machine has a finite safe run to a halting configuration outputting the mode-dependent access value.

**Proof.** Fix $k$ and induct strongly on $N=|z|-k$, generalizing $k$. The scan phase recognizes the encoded pair and exits with the comparison result $r=k$ (`accessCheck_pair`, `access_scan_run`). The data phase then returns false if $k$ is outside $z$, returns the mode-dependent value at position $k$ when $r=k$, and otherwise requests a counter bump (`access_data_run`).

If $k<|z|$ and $r=k$, the data phase's answer is exactly `accessValue mode z k`; the answer routine halts with that output (`access_answer`). If $k<|z|$ but $r\ne k$, the machine bumps the counter and resumes scanning at $k+1$ (`access_bump`). The new gap $|z|-(k+1)$ is smaller than $N$, so the strong induction hypothesis supplies the rest of the run; composing yields the result. Finally, if $k\ge |z|$, the data phase returns false, which is the access value beyond the end of the word, and the answer routine halts with that output. The encoded input has enough length to meet the scan and bump bounds, by the length formula for pair encoding (`Turing.length_pairEncode`).

**Key facts.** `Turing.length_pairEncode`, `Complexity.LogProg.accessCheck_pair`, `Complexity.LogProg.access_scan_run`, `Complexity.LogProg.access_data_run`, `Complexity.LogProg.access_bump`, `Complexity.LogProg.access_answer`.
