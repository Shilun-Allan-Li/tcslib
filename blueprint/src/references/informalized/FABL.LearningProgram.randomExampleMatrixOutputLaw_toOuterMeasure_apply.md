<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.randomExampleMatrixOutputLaw_toOuterMeasure_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Law on Events

**Claim.** The output law assigns any event in the output-and-cost space the same outer measure as the input law assigns the set of input matrices whose labeled output, with its specified learning cost, lies in that event.

**Proof.** The output law is the pushforward of the matrix-input law under the map that labels each input by the target and computes the stated output and cost. The outer measure of an event under a pushforward probability law is the outer measure of its preimage under the original law. Applying this pushforward preimage formula gives the claimed equality.
