<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.MultiTapeTM.liftSymbols_runFrom_over -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting Computations Over a Fixed Configuration

**Claim.** Under the stated independence from scanned input symbols and the prohibition on erasing a work-tape cell by writing a blank, lifting the Boolean computation over a fixed configuration $D$ commutes with running the machine for every number of steps.

**Proof.** The one-step compatibility theorem for lifting over a fixed configuration (`Turing.MultiTapeTM.liftSymbols_step_over`) says that one step of the lifted machine from the configuration formed by lifting $c$ over $D$ equals the configuration formed by lifting the result of one step from $c$ over $D$. Iterating this compatibility yields the same equality for $t$ steps: the function that lifts a Boolean configuration over $D$ intertwines the two step maps, and therefore also their $t$-fold iterates. Applying this to $c$ gives the claim.

**Key facts.** `Turing.MultiTapeTM.liftSymbols_step_over`.
