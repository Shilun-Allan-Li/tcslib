# Fill landing branches (backup of local branches)

Patch series of the local landing branches `land/{dl,3col,fac}`, each on #210 at `BASE.txt`, head in
`HEAD.txt`. Restore with `git checkout -b land/<x> <BASE> && git am -3 <x>/*.patch`. The PRs are opened
from these branches once #210 merges (DL before factoring). Records only; not a merge source.
