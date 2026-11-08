<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean :: Complexity.TQBFHard.reflTransGen_stepRel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded paths give step reachability

**Claim.** A finite path of encoded one-step transitions from the binary expansion of $u$ to the binary expansion of $c$ yields a reflexive transitive path from $u$ to $c$ under the encoded configuration step relation.

**Proof.** Induct on the given path. For a path of length zero, its endpoints coincide, so injectivity of binary expansion gives $u=c$; reflexivity then gives the desired reachability. For a path obtained by adding one final edge, write that edge as a step-language witness with source and target codes $c_1,c_2$. Repeatedly use injectivity of the pairing encoding to identify its input and the nested code components with those of the edge. Injectivity of binary expansion then identifies $c_1$ with the preceding path endpoint, $c_2$ with $c$, and the encoded window radius with $s$. The induction hypothesis gives reachability from $u$ to $c_1$. The original edge, with these identifications, is exactly a step-relation edge from $c_1$ to $c$, so appending it completes the path.

**Key facts.** `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`.
