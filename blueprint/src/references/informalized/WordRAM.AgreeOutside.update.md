<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.AgreeOutside.update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a memory inside a set

**Claim.** If $m'$ agrees with $m$ outside $s$ and $a\in s$, then updating $m'$ at $a$ to any word $v$ preserves its agreement with $m$ outside $s$.

**Proof.** Consider any address $x$ outside $s$. Since $a$ belongs to $s$, $x$ cannot equal $a$. Thus the update leaves $m'(x)$ unchanged, so the updated memory has value $m'(x)$ at $x$. The original agreement gives $m'(x)=m(x)$, and therefore the updated memory still agrees with $m$ at every address outside $s$.
