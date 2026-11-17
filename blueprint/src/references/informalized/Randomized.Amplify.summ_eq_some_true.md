<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.summ_eq_some_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of a singleton true list

**Claim.** A Boolean list has summary `some true` exactly when it is the singleton list $[\mathrm{true}]$.

**Proof.** Split by the list's shape. The empty list has summary absent. A singleton $[b]$ has summary `some b`, which equals `some true` exactly when $b$ is true. Any list with at least two entries has summary `some false`, so cannot have summary `some true`. Thus precisely the singleton true list satisfies the condition.
