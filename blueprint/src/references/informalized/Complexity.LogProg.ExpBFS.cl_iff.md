<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.cl_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle and Configuration-Code Reachability

**Claim.** Under the stated bound on $K$, a value is reachable from an initially accepted code by bounded oracle steps exactly when it is reachable from the initial configuration code by valid one-step configuration codes confined to the radius-$r$ window.

**Proof.** For the forward direction, take a witness initial value and an oracle-step path. The initial-oracle characterization (\texttt{ini_orcN}) identifies that witness with the initial configuration code. Each oracle edge on the path is, by the step-oracle characterization (\texttt{stp_orcN}), a valid configuration-code step. Replacing the edges gives the required code-reachability path.

Conversely, begin with a code-reachability path from the initial configuration code. Its starting value is below the exponential code bound by the configuration-code bound (\texttt{Codec.cfgCode_lt}), and hence below $K$. The initial-oracle characterization supplies the initial acceptance condition. Induct along the path: the reflexive case contributes no edges; at each extension, the step-oracle characterization supplies the corresponding oracle edge, while the bound on every code in a reachable path (\texttt{Complexity.ExpBFS.rcode_lt}) and the assumed inequality ensure its target is below $K$. Thus the path satisfies the bounded oracle reachability predicate.

**Key facts.** `Complexity.LogProg.ExpBFS.ini_orcN`, `Complexity.LogProg.ExpBFS.stp_orcN`, `Complexity.Codec.cfgCode_lt`, `Complexity.ExpBFS.rcode_lt`.
