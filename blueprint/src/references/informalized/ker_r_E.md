<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: ker_r_E -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Kernel of the coordinate restriction map is the complementary support submodule

**Claim.** Fix a prime $p$ and work in $V = \mathbb{F}_p^n \times \mathbb{F}_p^n$. For a subset $E \subseteq \{1,\dots,n\}$, let $r_E \colon V \to V_E$ be the restriction map that keeps the coordinates (in both components) indexed by $E$ and replaces every other coordinate with $0$. The claim is that the kernel of $r_E$ is exactly the support submodule $V_{E^c}$, where $E^c = \{1,\dots,n\}\setminus E$ is the complement: a vector $x$ satisfies $r_E x = 0$ if and only if $x$ vanishes on every coordinate lying in $E$ (equivalently, $x$ is supported on $E^c$).

**Proof.** We prove the two submodules are equal by showing each contains the other; fix a vector $x = (x_1, x_2) \in V$ and compare the two conditions on $x$. Recall the two definitions in play. First, $r_E x$ is the vector whose two components are the functions
\[
i \;\longmapsto\; \begin{cases} x_1(i) & i \in E \\ 0 & i \notin E,\end{cases}
\qquad
i \;\longmapsto\; \begin{cases} x_2(i) & i \in E \\ 0 & i \notin E.\end{cases}
\]
Second, $x$ lies in the support submodule $V_{E^c}$ precisely when $x_1(i) = 0$ and $x_2(i) = 0$ for every $i \notin E^c$; since $i \notin E^c = \{1,\dots,n\}\setminus E$ is the same as $i \in E$, this says exactly that $x$ vanishes on all of $E$.

1. **($x \in \ker r_E \implies x \in V_{E^c}$.)** Suppose $r_E x = 0$. The codomain of $r_E$ is the submodule $V_E$, carried as a subtype of $V$, so the equation $r_E x = 0$ first unpacks to the statement that the underlying vector of $r_E x$ is the zero vector of $V$ (passing from the subtype to its underlying value is the only purely formal step here). Reading this componentwise, both functions displayed above are identically zero:
\[
\bigl(i \mapsto \text{if } i\in E \text{ then } x_1(i) \text{ else } 0\bigr) = 0,
\qquad
\bigl(i \mapsto \text{if } i\in E \text{ then } x_2(i) \text{ else } 0\bigr) = 0.
\]
Now take any coordinate $i \notin E^c$; as noted, this means $i \in E$. Evaluating the two identities above at $i$ and using $i \in E$ selects the first branch of each conditional, giving $x_1(i) = 0$ and $x_2(i) = 0$. Since $i$ was an arbitrary coordinate outside $E^c$, this is exactly the membership condition for $V_{E^c}$.

2. **($x \in V_{E^c} \implies x \in \ker r_E$.)** Suppose $x_1(i) = x_2(i) = 0$ for every $i \in E$ (the membership condition for $V_{E^c}$, rewritten as above). We must show $r_E x = 0$, which again reduces to checking that each of its two component functions vanishes at every coordinate $i$. Split on whether $i \in E$:
   - If $i \in E$, the conditional selects $x_1(i)$ (resp. $x_2(i)$); but $i \in E$ means $i \notin E^c$, so the hypothesis forces $x_1(i) = 0$ and $x_2(i) = 0$, and the value is $0$.
   - If $i \notin E$, the conditional selects the else-branch, which is $0$ outright.

   In both cases every coordinate of both components of $r_E x$ is $0$, so $r_E x = 0$ and $x \in \ker r_E$.

Since each membership implies the other, the two submodules coincide, which is the assertion $\ker r_E = V_{E^c}$.
