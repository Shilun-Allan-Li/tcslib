# Computational reduction result

seq-zk-b proved all eleven public declarations in ComputationalReduction.lean. Final source
SHA256: 32d8ef575f769772b7e8b4b309ddf55d3e52c605c0f09c7fdc98cdbec11e6bb3; 271 lines.

The helper provides total packed metadata with exact length/projection/PT readers, the
normalized one-phase continuation and its PT proof, a uniform randomized suffix sampler,
and the advised nonuniform reduction with exact global-simulator/final-distinguisher tape
split. No witness enters the advice or machine. All old helper sources remain unchanged.

Native checks 01 and 02 both passed with zero diagnostics. Check 02 seals final bytes after
two proof-step comments were added: 3.28s, max RSS 2242215936 bytes. The all-declaration axiom
probe passed: only propext, Classical.choice, Quot.sound occur; no admission axiom. Raw logs,
search/overlap disclosure and static/style records accompany this result. This helper and
its evidence are future work after CP2 commit e978a28274fdeb545e622ae28747221088352512.
Root owns integration, the main theorem statements, final merged seals, commits and delivery.
