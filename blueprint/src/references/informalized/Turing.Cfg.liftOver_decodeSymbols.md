<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.liftOver_decodeSymbols -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting a Decoded Configuration

**Claim.** For an injection $e$ from Boolean symbols into $\Gamma$, lifting the configuration obtained by decoding a configuration's work-tape symbols and then lifting its symbols via $e$ recovers the original configuration exactly.

**Proof.** Compare the configurations component by component. Their states agree directly. Their input-head positions are the same numerical position, with only the finite bound transported across equal-length inputs. Each work-tape cell recovers its original content: decoding sends a symbol in the image of $e$ back to its Boolean preimage, and lifting sends that Boolean symbol back to the original symbol. Thus the condition in the definition of lifting holds at every cell, so the lifted configuration uses the original tape content there. The work-tape head positions also agree. Finally, decoding produces an empty output word, so lifting appends only the original output and leaves it unchanged. All components agree, proving equality.
