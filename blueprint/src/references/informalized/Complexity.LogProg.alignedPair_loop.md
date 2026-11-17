<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.alignedPair_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Aligned-Pair Scan Loop

**Claim.** Under the stated instruction, register-bound, and oracle assumptions, the scan reaches failure within at most $|w|$ symbols when the paired-tape parser rejects $w$. If the parser returns $(a,\_)$, it reaches done with register $r$ advanced by $\mathrm{stride}(2|a|+2)$. Every configuration before the end of either run satisfies the program precondition and keeps all registers at most $B$.

**Proof.** 1. Let the safety condition require both that the current configuration satisfies the program precondition and that every register is bounded by $B$. First note that updating only register $r$ to a value at most $B$ preserves all register bounds. The increment-chain fact (`Complexity.LogProg.arm_increments`) will provide safe runs through each block of advance states.

2. Establish the one-symbol scan step. If the current input word is $b::\mathrm{tail}$, its length makes the limit register strictly larger than $r$. Thus the scan comparison selects the first state. The first whole-input oracle call reads the bit at the current address, which is $b$ by hypothesis. The corresponding advance block increments $r$ by one stride, reaching the test state for $b$; the bound on the limit ensures that these increments stay within $B$. Each intermediate configuration is safe: the comparison uses distinct registers, and the call has the single argument $[r]$.

3. The empty-word case ends immediately: the scan comparison sees $r=\mathrm{limit}$ and enters failure. For a singleton word, the one-symbol step reaches its test state, where the updated register equals the limit; that comparison enters failure. This is a rejection case, with the claimed offset $t=1$.

4. For a word $b::c::\mathrm{tail}$, apply the one-symbol step and test the first bit. Since the register is still below the limit, the test proceeds to a read state. The second oracle call returns $c$, by the oracle hypothesis at offset one. If $b=c$, the read state selects the advance block for continuing the scan; if $b\ne c$, its prescribed branch either enters failure or advances to the state that completes the pair, according to the two bits. The two-step prefix uses at most two strides, and the limit equation bounds the resulting register values by $B$.

5. In the equal-bit case, the parser removes the doubled pair $bb$ and recursively scans the remaining tail, starting from the register already advanced by two strides. The shifted limit equation and the oracle hypothesis at offsets $i+2$ give exactly the assumptions needed for this recursive run. Concatenate the safe prefix and the recursive run. If the tail is rejected after $t$ further symbols, the original word reaches failure after $t+2$ symbols. If it parses as $(a,\_)$, its first component has acquired the leading bit, so its length is $|a|+1$; adding the two-stride prefix to the recursive final offset yields $\mathrm{stride}(2(|a|+1)+2)$.

6. In the unequal-bit cases, the parser either rejects at the current pair or reaches the completion state through the indicated advance block. The prescribed destinations and the two-step prefix give the asserted failure bound or the completed-run offset. In every case, the concatenation principle for safe reachability (`Complexity.LogProg.AReach.trans`) preserves the safety condition; one-step reachability (`Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`) records the instruction-by-instruction transitions. The whole-input call evaluates to the encoded input and current register word by the virtual-word identity (`Complexity.LogProg.vword_whole₁`).

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.arm_increments`, `Complexity.LogProg.AReach.trans`.
