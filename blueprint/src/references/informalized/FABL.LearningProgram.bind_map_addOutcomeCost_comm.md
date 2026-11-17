<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.bind_map_addOutcomeCost_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Commuting Cost Addition with Bind and Map

**Claim.** Adding a fixed extra cost after binding to the next-stage law with the first-stage cost added gives the same probability law as adding that extra cost to the first-stage pair before binding.

**Proof.** The bind-map identity rewrites the left-hand side as a bind whose first-stage distribution is the original law mapped by adding the extra cost. It remains to compare the continuation laws for a fixed first-stage pair. Write that pair as $(a,c)$ and a next-stage outcome-cost pair as $(b,d)$. On either side the resulting outcome is $b$, and the resulting cost is $e+(c+d)$ on one side and $(e+c)+d$ on the other. Associativity of cost addition makes these equal componentwise, so the continuation maps agree and therefore the two laws agree.
