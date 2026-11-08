# Audited encoding-adapter proof fill

Fill the 14 admitted theorem bodies in
`TCSlib/Cryptography/Encoding/BinaryArith.lean` against statement freeze
`6eec97be8f54d9990340900a5595dab32fb477f5`. The statement audit passes
0/0/0/3; its pasted report and dispositions are preserved under `audits/`.
The three definitions, their complete equation proofs, all 20 signatures,
namespaces and attributes stay fixed. Add no source declaration or private host.

Use draft PR #238 on `cryptography/lwe-sis-adapter-statements`, targeting
`cryptography/lwe-sis-constructions`, in `tcslib-lwe-sis-adapters`.
Root alone edits and runs native checks. The two internal research agents are
read-only and run no native/cache jobs. Existing owned pinned packages and the
adapter development objects belong to this chat; no other chat's objects or
packages are consumed or changed. No cache fetch is needed for these proofs.

Check each changed module through `scripts/lean_check_tree.sh`, serially, using
an explicit owned `TCSLIB_OLEANS`. At completion, run the exact scoped dependency
sweep in a newly empty own object tree and check every axiom/inventory row.
Keep all development failures separately identifiable. A passing statement gate
does not certify filled proofs or close source-policy/integration obligations.

**Ready to run — fill the 14 audited proofs with definitions and signatures fixed;
no merge or external dispatch is performed by this fill.**
