<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.toInt_wd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed interpretation of an encoded integer

**Claim.** If $v$ lies in the signed range for width $W$, then the signed integer represented by its $W$-bit encoding is $v$.

**Proof.** The signed interpretation of the encoding is the centered remainder of $v$ modulo $2^W$, represented in the interval from $-2^{W-1}$ up to but excluding $2^{W-1}$. The assumed inequalities $-2^W\le 2v<2^W$ are exactly the bounds placing $v$ in this interval after dividing by two. Therefore taking that centered remainder leaves $v$ unchanged, so the signed interpretation is $v.
