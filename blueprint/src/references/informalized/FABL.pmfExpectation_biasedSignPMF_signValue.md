<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.pmfExpectation_biasedSignPMF_signValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Biased Sign

**Claim.** For $p\in[0,1]$, the expected sign under the distribution with mean parameter $1-2p$ equals $1-2p$.

**Proof.** The mean of the coordinate-noise sign distribution with parameter $\rho$ and input sign $x$ is $\rho$ times the value of $x$ (\texttt{FABL.pmfExpectation\_coordinateNoisePMF\_signValue}). Take $\rho=1-2p$ and $x=1$. The parameter lies in $[-1,1]$ when $p\in[0,1]$ (\texttt{FABL.biasMean\_mem\_Icc}), and the value of the input sign $1$ is $1$. Hence the expectation is $1-2p$.

**Key facts.** `FABL.biasMean_mem_Icc`, `FABL.pmfExpectation_coordinateNoisePMF_signValue`.
