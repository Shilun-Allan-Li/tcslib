<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsPlaced.succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor placement invariant

**Claim.** If the placement invariant holds for the first $i$ items and the layout preconditions hold, placing item $i$ at its sort position and advancing its key's counter to one past that position gives the invariant for the first $i+1$ items.

**Proof.** Write $p(j)=\mathrm{sortPos}(kf,A.n,j)$. First fix a key $t<A.nb$. By `cntEq_succ`, its count among indices below $i+1$ is its count below $i$, with one added exactly if $kf(i)=t$. If equality holds, the counter update is at the cell for $t$; its new value is $p(i)+1$. By the definition of $p(i)$, this is the previous base count for keys below $t$, plus the count of key $t$ among indices below $i+1$. If equality fails, neither the count nor the cell for $t$ changes, so the previous invariant supplies the result.

Now consider a placed item $j<i+1$. The sort position bound (`sortPos_lt`) ensures $p(j)<A.n$. Since the destination and counter ranges are apart, the counter update cannot affect the destination address $A.dst+p(j)$. The update at item $i$'s destination can affect this address only if $p(j)=p(i)$. The sort-position injectivity fact (`eq_of_sortPos_eq`) then forces $j=i$, which is impossible when $j<i$. Thus for $j<i$ both updates leave its cell unchanged, and the previous placement invariant applies. For $j=i$, the destination update sets its cell to $it(i)$, as required.

**Key facts.** `Light.cntEq_succ`, `Light.sortPos_lt`, `Light.eq_of_sortPos_eq`.
