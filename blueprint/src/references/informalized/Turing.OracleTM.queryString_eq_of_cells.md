<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.queryString_eq_of_cells -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query String Determined by Its Cells

**Claim.** If the query tape contains the symbols of $w$ in positions $0$ through $|w|-1$ and is blank at position $|w|$, then its query string is $w$.

**Proof.** The blank cell at position $|w|$ ensures that the first blank position used to define the query string occurs no later than $|w|$. It cannot occur earlier: if the first blank were at some position $m<|w|$, the assumed cell condition would say that this cell contains the symbol $w_m$, contradicting that it is blank. Thus the first blank position is exactly $|w|$. By the definition of the query string, it is the list of cell contents before that position. To see this list is $w$, one can induct on its length: the empty prefix gives the base case, and extending a prefix by one position appends the corresponding symbol of $w$. Taking the prefix of length $|w|$ yields $w$.
