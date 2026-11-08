<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.cfgRecord_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Record of an Initial Configuration

**Claim.** The record of the initial configuration has the stated state, input-position digits, blank work-tape fields with a head mark at offset $s$, and tag.

**Proof.** Substitute the initial configuration into the record encoding. Its state is $q_0$, its input-head value is $1$, every work-tape cell contains the blank value, and each work-tape head is at position zero. At the cell indexed by $j$, the head mark is therefore true exactly when $0=j-s$, equivalently when $j=s$. Thus every work-tape field is the same list of length $2s+1$ with precisely the indicated marked cell; the $k$ such fields form the stated replicated list. The tag remains the singleton containing $\tau_0$.
