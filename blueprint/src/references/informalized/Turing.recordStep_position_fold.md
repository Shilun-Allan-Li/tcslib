<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_position_fold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Position Fold Over Binary Digits

**Claim.** Scanning the digit symbols of a Boolean word from count zero and a true flag leaves the word unchanged, returns count $\min(2,|w|)$, and records whether its base-two value is zero.

**Proof.** First compute the fold on the word itself. By induction on the word, starting with count $a$ and flag $b$ yields count $\min(2,a+|w|)$ and flag $b$ conjoined with the assertion that every bit of $w$ is false. The empty case is immediate; in the cons case, the fold increases the count by one, capped at two, and conjoins the flag with the negation of the first bit.

A second induction identifies the all-false assertion with the statement that the base-two value of the word is zero: the empty word has value zero, while adjoining a leading bit gives zero exactly when that bit and the remaining word's value are both zero. Finally, `scanResult_fold` converts the scan with a fold-forward update and a keep-on-return update into precisely this fold, preserving the word. Substituting $a=0$ and $b=\mathrm{true}$ gives the claimed count and zero-value flag.

**Key facts.** `Turing.scanResult_fold`.
