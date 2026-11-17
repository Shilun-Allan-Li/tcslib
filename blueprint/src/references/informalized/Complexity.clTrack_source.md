<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTrack_source -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One tracking step simulates a source step

**Claim.** From the canonical configuration for $c$ and a valid boundary tag $b$, one tracking step enters the bank phase with initialized control states determined by the source-head displacements, while retaining the counter values; the new tag is valid for the successor input-head position.

**Proof.** Apply the reference-action simulation property (`Complexity.clRef_apply`) to the source transition, using the boundary condition on $b$. It yields a tag valid for the successor and describes the resulting reference configuration after the source transition and the prescribed administrative actions. In the canonical tracking configuration, the virtual-input buffer at its head contains exactly the source machine's current input symbol (`Turing.FinTM.bufferTape_inputSymbol`), and the remaining source work-tape symbols likewise agree with those in $c$. Therefore the tracking machine's transition receives precisely the source transition's inputs. Its unbanked branch performs the reference action while initializing the bank control states according to the source displacement vector. The counter tapes are unchanged, so their stored binary representations remain those of the assigned values.

**Key facts.** `Complexity.clRef_apply`, `Turing.FinTM.bufferTape_inputSymbol`.
