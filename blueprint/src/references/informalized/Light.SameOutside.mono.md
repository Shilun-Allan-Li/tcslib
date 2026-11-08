<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SameOutside.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity outside an interval

**Claim.** If two integer-valued sequences agree outside $[a,a+n)$, and $[a',a'+n')$ contains that interval, then they agree outside $[a',a'+n')$.

**Proof.** Fix an index $b$ outside $[a',a'+n')$. Thus either $b<a'$ or $a'+n'\le b$. In the first case, $a'\le a$ implies $b<a$; in the second, $a+n\le a'+n'\le b$. Either way, $b$ is outside $[a,a+n)$, so the assumed agreement gives $\mu'(b)=\mu(b)$.
