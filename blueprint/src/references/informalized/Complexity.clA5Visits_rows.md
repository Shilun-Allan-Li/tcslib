<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Visits_rows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visit Rows as an Ordered Row Stream

**Claim.** The first $N$ visit rows equal the ordered stream of $N$ rows whose time-$t$ entries, in tape order, are the optional-time codes for the greatest strictly earlier visits to the current work-head positions on the specified all-zero input.

**Proof.** Proceed by induction on $N$. For $N=0$, both streams are empty. For the successor case, the induction hypothesis identifies the first $N$ rows. The recursive definition appends the visit row at time $N$, and the exact-row identity says this appended row is precisely the list of codes prescribed for each tape at that time. This is exactly the next row appended by the generic stream, so the streams agree through $N+1$ rows.

**Key facts.** `Complexity.clVisitRow_exact`.
