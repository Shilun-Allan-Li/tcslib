<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.relativeHammingDist_booleanFunctionF₂Encoding_coordinateSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance Under Binary Encoding

**Claim.** The relative Hamming distance between the binary encoding of a Boolean function and the sum modulo $2$ of coordinates in $S$ equals the relative Hamming distance between the original function and the product of the corresponding sign coordinates.

**Proof.** Express each relative Hamming distance as the uniform probability that the two function values differ (\(\texttt{uniformProbability\_ne\_eq\_relativeHammingDist}\)). Reindex the first probability along the bijection from the binary cube to the sign cube, so both probabilities are averages over corresponding inputs. At each binary input, the encoded function agrees with the coordinate sum exactly when the original sign-valued function agrees with the product of the selected sign coordinates: the transport identity for parity identifies the latter product with the sign encoding of the coordinate sum (\(\texttt{binaryParitySign\_transport\_eq\_parityFunction}\)), and encoding the binary function recovers its original value (\(\texttt{signEncode\_booleanFunctionF₂Encoding}\)). Thus the two disagreement indicators agree at every input, and so do their uniform averages.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.binaryParitySign_transport_eq_parityFunction`, `FABL.signEncode_booleanFunctionF₂Encoding`.
