<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.aI_cfgWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a configuration word

**Claim.** Let $N$ be a nondeterministic Turing machine with Boolean input alphabet, let $x$ be a finite bit string, and let $C$ be a configuration of $N$ on input $x$ whose work-tape heads and nonblank cells lie within distance $s$ of the origin. For either bit $b$, scanning the configuration block of the encoded word of $C$ and decoding its input-head position gives the effective action of $N$ on $C$ with transition bit $b$; the scan also recovers the head and output summary of $C$.

**Proof.** 1. Apply the configuration-word scan theorem (\texttt{Complexity.Codec.vScan_cfgWord}) to the first $2s+1$ cell blocks. It says that the scan records the head and output summary of $C$, and that for each work tape its stored symbol is exactly the symbol under $C$'s head. The head-summary component is therefore precisely the encoding of $C$'s state and output summary.

2. Use this head-summary equality in the definition of the scanned action. The remaining input to that action is decoded from the portion of the word after the cell blocks. The encoded word’s position lemma (\texttt{Complexity.Codec.cfgWord_pos}) identifies this portion, up to the prescribed input-position width, with the padded binary representation of $C$’s input-head position. Its binary value is that position by the padded-bits identity (\texttt{Complexity.Codec.bitsVal_padBits}). The input-symbol identity (\texttt{Complexity.Codec.inputSymbol_eq}) then identifies the decoded symbol with the symbol of $C\) under its input head.

3. The scan theorem’s work-tape component supplies the exact work-tape symbols under the heads. Thus the effective action receives the same state, input symbol, and work-tape symbols as the action assembled from the scan, with the same transition bit $b$. This proves the action equality, while the head-summary equality from the first step proves the other conjunct.

**Key facts.** `Complexity.Codec.vScan_cfgWord`, `Complexity.Codec.cfgWord_pos`, `Complexity.Codec.bitsVal_padBits`, `Complexity.Codec.inputSymbol_eq`.
