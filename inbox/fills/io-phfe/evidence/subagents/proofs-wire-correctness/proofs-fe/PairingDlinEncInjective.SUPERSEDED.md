# Superseded manual DLIN parameter reconstruction

PairingDlinEncInjective.lean.inc is superseded for integration by
PairingDlinEncInjectiveShared.lean.inc under root's shared-parameter-codec decision.
The original candidate and notes remain unchanged as archived scratch evidence.

Archived source SHA-256: e455569bac4b90ab13fd7c04fa087a4bdf8d1d78072d77709c03599b22c45269
Archived notes SHA-256: a8b09bc777d84a33470eda5d37d8e35a1118d38a59e9dcb098da31bda1463750

Replacement reconstructs pp.encode equality from the first two WORD equalities, then uses
pending PublicParams.encode_injective to align pp before five point injections. No manual
PublicParams/GroupDescription reconstruction remains. Frozen main header/prose unchanged.
Neither archived nor replacement candidate is claimed native verified by this marker.
