# Short-query SAT clock bound

For a SAT query of length m at most floor(log₂ n), the existing search
clock b·2^(m+1)·(a·(2m+2)^d + (2m+2)^2) is bounded by
2b·(a·2^d+4)·(n+1)^(d+3). The scratch proof checks the zero-length case and
allows arbitrary natural a, b and d. It elaborated with standard axioms.

This supplies the arithmetic bound for using the proposed exact linear
SAT verifier on short queries. The verifier interface and the Ladner
implementation remain separate obligations.
