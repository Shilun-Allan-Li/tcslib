# Audit bundles removed from the working tree

The campaign's dispatched audit bundles (`audits/*-bundle.md`) were removed from the working
tree on 2026-10-15 (user), before the campaign's merge to `main`: 75 files, 122.8 MB. Each is the single file an auditor received: the pack verbatim, then its
attachments. Packs, findings, resolutions, evidence and logs stay in the tree. From now on
bundles are not committed (`workflow.md`, Artifacts): the resolutions record each bundle's SHA-256
and section count, and the local dispatch folder keeps the file.

Every bundle below is retrievable from history at the last commit that has it:

```
git show fc95f12cfbdf57d0bc979e017f2fd9b94ddb6192:<path>
```

The 35 bundles committed before the campaign (already on `main`) are unchanged.

| Bundle | Bytes | SHA-256 of the committed file |
|---|---:|---|
| `audits/12.2c-t1-blockloop-bundle.md` | 699,282 | `e2a8d776e966c1e32d3c08db2a56f4e9de897a9894f5791f9a8bc089c0b0529d` |
| `audits/12.2c-t1-codeformat-bundle.md` | 827,974 | `7217ecfd6d40803135cb8845e917226d885d124c6f42fca71ea122364d05931f` |
| `audits/12.2c-t1-loop-bundle.md` | 1,897,088 | `38385fc0b11ad399fe8a8833398c4e326e2181dcc546e23f80449d8bc49378e4` |
| `audits/12.2c-t2a-bundle.md` | 2,886,804 | `11c9cb27a0b4f284a0809c4ef60781d484c90d4b83784b3c23a66919bc5940a0` |
| `audits/arm-extensions-fill-bundle.md` | 4,876,691 | `1654682d03921a615e542f1c5e963cac7081428cf2159c9c1c41cbcee114196c` |
| `audits/b1-fill-bundle.md` | 1,101,801 | `3c5662b5842cbffb84ac92eb88c0a9223c20a46a2b792dd6c6652a363b1c3996` |
| `audits/b2b-fill-bundle.md` | 2,815,590 | `50ce1a937a31d856d6d18eb038a1182cf1997077913d57aa5fa835d9071dae39` |
| `audits/b6-hosts-statements-bundle.md` | 3,704,395 | `692e5822fa6b66693710c4226c1071f0c1bde3b97d6df3bfbf13cddf0b9e641e` |
| `audits/b6-restatement-bundle.md` | 2,330,323 | `a7e8c5049b94951ca58347b97c39760f8f68a359ffb26f8196e3b87129af71df` |
| `audits/b7-fill-bundle.md` | 1,653,769 | `895963b139a52effba3cc4a4db16d766925f3903ac895474c88b40fd167ea991` |
| `audits/b7-statements-bundle.md` | 448,764 | `fe9d45215936c31ec23181795800548701d6ed0271773c3c6fc680bb3e73506f` |
| `audits/b8-fill-bundle.md` | 1,055,884 | `0281bc16fd9ed01282aff63f069c1469158d8bcae478376cd9773a6d5e324cfe` |
| `audits/c1-hosts-statements-bundle.md` | 3,653,998 | `8d4ba59b410fab2ddc93e80b81abe76e9c73d76bc3eb294c73456de78aceb65b` |
| `audits/ch3-p31-bundle.md` | 461,158 | `37d2fd94ac5539a756cbba23c826a21882449a3bc4d10c3da0131446f8421281` |
| `audits/ch3-p32-bundle.md` | 436,116 | `dbfadcfbc77ef508a89e927ab2d04c122c6ab65ddac98462e85fe0c0547c3e2a` |
| `audits/ch3-p32-r2-bundle.md` | 719,797 | `9de1defa7ecd5a188b355152349d3d88df3d475a61fa94887081fb2ad15a153f` |
| `audits/ch3-p33-bundle.md` | 533,633 | `45339e257283d441ad0afd38a6ed9d6c563ef72688a3f6b6e58b833e3b031ee1` |
| `audits/ch3-p33-r2-bundle.md` | 585,888 | `fedeadf847a95c6ba78f7a0e377a76a922df3ca7f5ad97f3d3b7eef1620be99a` |
| `audits/ch34-b3a-fill-bundle.md` | 3,200,946 | `7770623f02b3312899f936634f0164e8ab355b0e7a32d51f5aec7122e55170e2` |
| `audits/ch34-b5b-fill-bundle.md` | 3,315,080 | `6e4ad39959ca9b0387f045a9f9958aff03a062dc3283be42fed41332dcc578f5` |
| `audits/ch34-b5b-fill-r2-bundle.md` | 5,798,939 | `ece01962a179170cbe658e4777f8b9df1cd5d4dca525289f9b6d6a3750ca010b` |
| `audits/ch34-c1-fill-bundle.md` | 1,888,688 | `0c415079d007c6d65b590a2951ec78492a7677cdd7475858e001250133916bdd` |
| `audits/ch34-p0-bundle.md` | 865,996 | `69f84b8d7194081e3b7749467f41f2c77fc3f09409e655badac32a4ae6b3d05b` |
| `audits/ch34-p0-r2-bundle.md` | 1,591,987 | `cb809b78da0fa2c308158c6722bdf8606bb7c002cd18f50c937b2b3f34cabb8d` |
| `audits/ch4-p41-bundle.md` | 489,135 | `58bdb7680b3bfe2f888509ed81a0fbc75e15197647c13150f995fc22a30c31de` |
| `audits/ch4-p42-bundle.md` | 370,354 | `5139d5aeeb9009888da2101c6a63ef70acf029a35265d567c8b7441db4de785c` |
| `audits/ch4-p43-bundle.md` | 329,177 | `5a52f3982128502b46dfe4914df2ebbcec22d1a792d0df5373b6d348210e9f1e` |
| `audits/ch4-p43-r2-bundle.md` | 421,852 | `beb69f18e8fc8cd53cf277195dfb3d04d7d47cab6c8faa7c9df080a75919dbb7` |
| `audits/ch4-p43-r3-bundle.md` | 443,609 | `6a04a9ccd659ef32b053e6158c294e91377f492aacb1dd8fd19e1ab3432f5ea0` |
| `audits/ch4-p44-bundle.md` | 379,024 | `899d3c43d6576dff48f96dccaee4b56370699563ee03b2cc010eea96072698ca` |
| `audits/ch7-fill-bundle.md` | 400,756 | `39eacf62f4389fc12130f491a306536b284033261b9733105dbc4e358ef5ce9d` |
| `audits/ch7-fill-r2-bundle.md` | 380,597 | `4c8d52b6e01e37c49e5883a5d9eb808b8271026d42b9dbf8c85e2b667ac46447` |
| `audits/ch7-phase1-bundle.md` | 287,094 | `b316e2a523333ce40e91b9bd254c52d0110daf0651d582ccf258343e16c8b53e` |
| `audits/h2-promotion-bundle.md` | 1,975,184 | `3b9b166e4b282a7c84026a92472dd7b868f6c19323390ae4aac1bcbbe6219bfc` |
| `audits/h2-promotion-r2-bundle.md` | 3,004,595 | `6bc5f4154d0bc5e63c67d5bec5156a4a6568ae5a3a3945a1e98d8ee5693223d8` |
| `audits/mig0a-bundle.md` | 2,072,129 | `2147706acf81c096d4d9820772596fc9499df8d6b771f21e41c8f965460aa130` |
| `audits/mig0a-r2-bundle.md` | 2,255,983 | `84b72f4130165286c3ab85bc4879638c06ff8b55e037e722a3e63c796f64f7a1` |
| `audits/mig0b-bundle.md` | 3,654,697 | `e0dc9e0ad89efe42b037a44ffcd6afe003d5746f6c10383972204c17a53cb66a` |
| `audits/mig0b-r2-bundle.md` | 4,884,701 | `3e697e9e588fe1eca2669de01b1c47c5c61cc7af8a816095f18fbde9fa9559fb` |
| `audits/mig1-statements-bundle.md` | 3,083,017 | `1095a89fc0ac971c240ff53a8cad00b378aac13a877d7a8792aeb8309fb2803a` |
| `audits/mig1-statements-r2-bundle.md` | 4,151,848 | `6acaad71a9bea8fb60a1b9008a41634cb079392f7df77021b24bac6d7bce1bd0` |
| `audits/programs-vendor-bundle.md` | 1,575,982 | `9c474726a4a48c2d85d23df60267c78b7da4b64a7d267cc8b3370841b85c6e6a` |
| `audits/rd2-statements-bundle.md` | 2,699,513 | `b873469afca84f2683f18f9ec2a2d1f73972527dfc3b0fa6aeb25d11e8a3c15f` |
| `audits/retrofit-r1-bundle.md` | 393,129 | `3d0a0f7415f22caa60ff21a9c11747eef2f786c4b0bfd8e5c36140c221c4200e` |
| `audits/retrofit-r1-r2-bundle.md` | 1,469,835 | `6902983404d5563980943e2795d21fb786acc563b5dcec31cf3e4c96ddd0b819` |
| `audits/retrofit-r1-r3-bundle.md` | 902,086 | `b7ba3df87f3d46bf28f5829f318369415c1bd23f0f497ae780dcefef9d682755` |
| `audits/retrofit-r1-r4-bundle.md` | 810,637 | `e1bc46ba88ca93481bbf91c4d0fa4db7ea140cd0102a0bd7333a9b724004b70e` |
| `audits/retrofit-r1-r5-bundle.md` | 1,102,586 | `2b6e739d344e009cef8ba82c9ff0090857a127b489fd6a0eded5efc4937c5492` |
| `audits/retrofit-r1-r6-bundle.md` | 1,133,066 | `2d84aef2921ce6070a14b8b319c7830cfa5161e58f0ce7eea239d00de2ffd30c` |
| `audits/retrofit-r1-r7-bundle.md` | 1,605,493 | `cf7ff7fe7095c3a58f1040640e9f3c8788faeed73e54cf3e3e1367873acded6e` |
| `audits/retrofit-r1-r8-bundle.md` | 1,618,177 | `347f20e5ffd0f367bf57d7c39cd47e75661d121c6893c421897171ed8bc82158` |
| `audits/routine-f1-bundle.md` | 538,601 | `b610b75e630db240448226dd87ca960f0669a074e1a1efcd34e4e4cbf57833bb` |
| `audits/routine-f2-bundle.md` | 1,481,767 | `72861b805fcbe8f368905149e21d39aa827a6b3c052809582709438d874a8004` |
| `audits/routine-infra-bundle.md` | 991,847 | `e9216b8b59eeb749484ba6f3f956ced25e7a55fe900c859924a0339e5bef4673` |
| `audits/routine-infra-r2-bundle.md` | 1,196,634 | `fc7afcb8a469914c4b6a672348769329cfe708c013c64cfbb957481aadb2a3cf` |
| `audits/routine-infra-r3-bundle.md` | 1,184,720 | `bb6514407d11a4a72b9dd4ad6d20a7acffd01a564fe3d369afbb49f30248d89b` |
| `audits/s12-8-fill-AC-bundle.md` | 6,433,348 | `696c665db7d2ef4a57206b4af6fd5f7ac934aa2a25c15ec94a19e58b27e45d88` |
| `audits/s12-8-fill-D-bundle.md` | 1,012,338 | `5564ab859bc4b8234d79aaa74c5a43494a075fb9930a2228f66b14194dd3ce5d` |
| `audits/s12-8-fill-D-r2-bundle.md` | 1,693,558 | `d3a4a4e15d20accdc3c58c6401c42df5ff91d9375fc048af2fe7bad77b166199` |
| `audits/s12-8-statements-bundle.md` | 1,871,645 | `8bd755ca746d78751c2168a4b4fb16f8971d2613f6f3827ef8d548b3cd7e81fb` |
| `audits/s12-8-statements-r2-bundle.md` | 1,951,193 | `7e8a21e9af807f501b7d092d2b74e5c11b50e4734281e5968b4aef670d0a3c07` |
| `audits/s12-counter-bundle.md` | 1,010,702 | `b94d9648b0cea831fb91b2ee17155e0a4e88f08661dc9504d43fd2d71a360b5a` |
| `audits/s12-counter-fill-bundle.md` | 1,617,922 | `e28c3eefbb721282f8992bf8a403abe8246a06973ab95ac14895d28845a0e537` |
| `audits/s12-framed-bundle.md` | 822,270 | `5ae388dc2f33f884646b4f513f80ec5783e4ee38fe3d4185cf7ac3345a6a1634` |
| `audits/s12-framed-fill-bundle.md` | 1,196,924 | `ea9b8b7d9446e921645a601d809b34eecbc697ba1af615595a9435e7f88f835d` |
| `audits/s13d-g1-bundle.md` | 1,506,164 | `29e30d9b49e681bb43223974e50813242c420e84aac9513d89c17c1869ee39c0` |
| `audits/stage2-statements-bundle.md` | 2,284,580 | `28b7f2c805088d35209cb67a1c652d2e8d7087b4bbba2a360dd5216df9354191` |
| `audits/vhost-f1-bundle.md` | 355,863 | `ea9dd29d12323f2b7f1b5088b2bb6dc871c3c1b0212b6e026bca91f66eb48d2c` |
| `audits/vhost-infra-bundle.md` | 348,279 | `b76a53aa8be41c5eb80700e2b5cdb91aa831f367ce213fe51ce6d2eb490bee64` |
| `audits/wave1-fill-bundle.md` | 6,630,042 | `1c7218cde8a4106d2c78aed6880fccb2308db1709158c6266b966746de0e7c33` |
| `audits/wave1-statements-bundle.md` | 1,627,317 | `e0c798f5d338ac25abede3703c96a6f58c47aad88b71490714487bceffa28356` |
| `audits/wave1-statements-r2-bundle.md` | 2,846,784 | `23332cb7df9647bc3c88a5c27000203cb0921a047142622cf6002ad721ca2a70` |
| `audits/zone-infra-bundle.md` | 370,851 | `58e86447461c2f68c02fb616b90059ba845f5623add84adac7c14a519385c2d0` |
| `audits/zone-infra-r2-bundle.md` | 322,120 | `e78257a8a4b7fe2917470d1eeb2784098e09d71c4ba13396a655160b3bff3cc8` |
| `audits/zone-infra-r3-bundle.md` | 219,755 | `081535e127c51bb2872ed146c3d7801c212f91b9c6e511764f14076f7c1966d3` |
