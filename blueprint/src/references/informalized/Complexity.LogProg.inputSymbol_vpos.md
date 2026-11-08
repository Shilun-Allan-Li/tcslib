<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.inputSymbol_vpos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Virtual input symbol at a segment position

**Claim.** For a valid virtual position in a segment of a virtual word, a configuration whose input is that virtual word and whose input head is at the corresponding offset sees the symbol prescribed by the segment position.

**Proof.** First use the input-head position identity ($\texttt{Turing.FinTM.inputSymbol\_at}$): when the head position is one more than an input index, the scanned symbol is the optional list entry at that index. Split according to whether the requested segment position is the left boundary, an internal cell, or the right boundary.

At a left boundary, the offset is the beginning of that segment. For the first segment this is the input boundary and the symbol is absent; for a later segment, the offset formula ($\texttt{Complexity.LogProg.off\_succ}$) places the head just after the preceding separator, so the separator's second bit is read. The separator-position identity ($\texttt{Complexity.LogProg.getElem\?_vword\_sep}$) confirms this location and symbol.

At an internal cell $c$, validity gives $c$ within the segment's word. Its within-segment offset is strictly less than the rendered segment length ($\texttt{Complexity.LogProg.cellOff\_lt}$), so the segment-position identity ($\texttt{Complexity.LogProg.getElem\?_vword\_seg}$) reduces the virtual-word lookup to the rendered segment. An undoubled segment contributes its $c$th bit directly; in a doubled segment, the doubled-word lookup identity ($\texttt{Turing.getElem\?_dbl}$) shows that either copy at offset $2c+p$ has that same bit.

At a right boundary before the final segment, the offset is the end of the rendered segment, which is the first separator bit by $\texttt{Complexity.LogProg.getElem\?_vword\_sep}$. At the last segment's right boundary, the final-position identity ($\texttt{Complexity.LogProg.vpos\_right\_last}$) puts the head at the input's right boundary, where the scanned symbol is absent. These cases give exactly the symbol specified by the virtual-position map.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Complexity.LogProg.off_succ`, `Complexity.LogProg.getElem?_vword_sep`, `Complexity.LogProg.cellOff_lt`, `Complexity.LogProg.getElem?_vword_seg`, `Turing.getElem?_dbl`, `Complexity.LogProg.vpos_right_last`.
