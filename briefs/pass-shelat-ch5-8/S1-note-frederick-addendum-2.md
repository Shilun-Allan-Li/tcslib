# Second addendum to the S1 note for Frederick Dehmel (draft for Seyoon to forward)

Drafted 2026-11-05 by the ch. 5–8 maintainer session. Status: **draft, not sent.** It reports the
merge of `main` into the branch and makes one small request (F-5).

---

Hi Frederick, one more follow-up: the merge of `main` into your branch, with one small request.

**What happened.** Seyoon ruled to merge `main` into `cryptography/pass-shelat-ch2-4` through a
PR, after a full replay. The merge is `87b5b37c6f21fcea58f9274a519b1d530d83c257`, on the branch
`integrate/main-into-pass-shelat-ch2-4`. It merges `main` at
`7d36bbc27dfabd4988ee1702bc342049a1f3e006` into your branch at
`1a338385e7e1f67522987162322bee0948c96f3b`. The two conflicts were the trivial ones from the
first addendum, resolved by union.

**The replay.** 418 modules were each checked alone into a fresh olean tree: 406 pass, 12 fail.
- Three are the known `zipWith_xor_ofFn` clash (S1 note, point 1): `Asymptotic/MultiMessage`,
  `Asymptotic/PublicKey` and the `Asymptotic` facade. The merge did not cause them.
- Nine are caused by the merge.
  - `ZeroKnowledge/ThreeColoring/ProtocolProofs.lean` fails with 7 "Ambiguous term
    `pairEncode_ne_nil`" errors, at lines 175, 211, 219, 222, 239, 242 and 246.
  - The eight modules after it cannot import it.
  - The cause: `main` added `Complexity.pairEncode_ne_nil`
    (`Complexity/SpaceComplexity/Logspace/InputAccess.lean:83`), the same fact as your
    `ColMachines.pairEncode_ne_nil` (`ThreeColoring/Machines.lean:969`). `ProtocolProofs` opens
    both `Complexity` and `ColMachines`.

**A correction to the first addendum.** It said a scan of the merged tree finds no new clash of
full declaration names. That is still true, but the scan compared full names only. It could not
see a short name made ambiguous by two `open`s, which is what broke.

**Request F-5.** Could you qualify those 7 uses, for example as `ColMachines.pairEncode_ne_nil`?
- **Tested.** In a scratch copy of the merge, uncommitted and reverted afterwards, the
  qualification makes `ProtocolProofs` and the 10 modules after it pass, with 0 errors. The only
  `sorry`s are your existing three (`ThreeColoring/Protocol.lean:784, 853`;
  `Simulator.lean:766`). The `ZeroKnowledge` facade still fails, on the `zipWith_xor_ofFn` clash
  only.
- **Line 175** would become 116 characters long, so it wants a line break.
- **It needs nothing from `main`.** `ColMachines.pairEncode_ne_nil` already exists on your branch,
  so the change can land there first. We then merge `main` again and replay.
- **An alternative**, your call: after the merge, drop your copies in favour of `main`'s
  `Complexity.pairEncode_ne_nil`. It has the same statement, over the same `pairEncode`, and the
  branch has two more copies, in `Asymptotic/GGMReduction.lean:138` and
  `ZeroKnowledge/GraphIsomorphism/Proofs.lean:389`. Qualifying is the minimal fix.

Thanks.
