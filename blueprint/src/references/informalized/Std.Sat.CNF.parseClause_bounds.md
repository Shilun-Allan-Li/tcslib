<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseClause_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for a successful clause parse

**Claim.** If parsing a bit string $x$ as a clause with fuel $f$ returns clause $C$ and remainder $r$, then $|r|\le|x|$, and each literal $(v,b)$ in $C$ satisfies $v+1+|r|\le|x|$.

**Proof.** Induct on the fuel, generalizing the input, clause, and remainder. With zero fuel, the only successful case is an input beginning with the clause-ending bit; the parsed clause is empty and the remainder is the tail, so its length is at most the input length and there are no literal bounds to check. For positive fuel the same terminating-bit case applies. If the input begins with a continuation bit, successful parsing must first decode a literal and then successfully parse the remaining clause from the leftover bit string. The length identity for a parsed literal (`Std.Sat.CNF.parseLit_length`) gives the exact length consumed by that literal: its variable index plus three marker bits, plus the length of the leftover string. The induction hypothesis bounds the later remainder and every literal in the recursively parsed clause relative to that leftover string. The exact consumption identity transfers those bounds to the original input; it also gives the required bound for the newly parsed first literal. Thus both the remainder-length bound and all literal bounds hold for the resulting clause.

**Key facts.** `Std.Sat.CNF.parseLit_length`.
