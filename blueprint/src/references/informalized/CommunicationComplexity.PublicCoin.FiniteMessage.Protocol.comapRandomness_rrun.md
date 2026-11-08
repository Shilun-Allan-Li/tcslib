<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.comapRandomness_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized execution after reindexing

**Claim.** Executing the protocol reindexed along $h\colon\Omega'\to\Omega$ with randomness $\omega$ gives the same output as executing the original protocol with randomness $h(\omega)$.

**Proof.** Randomized execution runs a deterministic protocol on the paired inputs. The deterministic comap execution law states that running a protocol after precomposing its input maps is the same as running the original protocol on the images of those inputs (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap\_run}). Here both input maps send $(\omega,x)$ and $(\omega,y)$ to $(h(\omega),x)$ and $(h(\omega),y)$, respectively. The resulting run is therefore exactly the original randomized execution at $h(\omega)$.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
