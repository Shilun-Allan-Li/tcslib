# FE9 source-slice and capture-byte binding addendum

This clarifies two exact byte identities without changing the frozen2837-file
packet. `SOURCE-FREEZE.json`'s `full_chunk_SHA256` hashes the actual source slice
without a terminal newline. Every saved chunk capture is that exact slice plus
ONE LF; `MANIFEST.json` hashes the complete saved capture bytes. All18 cases
below match actual Git source at BASE9b5 or HEADd64, and the original source
ranges. Offsets are Unicode code-point positions, not UTF-8 byte offsets.

| # | Phase · declaration | Slice bytes | Capture bytes | Exact source-slice SHA256 | Actual capture-byte SHA256 |
|---|---|---:|---:|---|---|
| 1 | BASE · `Complexity.enumCont_first_anchor` | 1364 | 1365 | `9b6e3f316ac08206ab2a27c6affc0e48ab4cd54544f282e2486806015ce0c028` | `ff40ad8319ccf907d9483b514911030a4a991a7383fbea31b0ab347fb70de6f3` |
| 2 | HEAD · `Complexity.enumCont_first_anchor` | 1573 | 1574 | `7f30c6a2909ad3bb42fdc055d139783186f0768afc7288bc1ca91c1219ef1a46` | `88ebca572c35cc11a02cff2d652eb9d5fb741211fd43567af9a71e6cf6b9ec24` |
| 3 | BASE · `Turing.xr_firstArrival` | 1161 | 1162 | `fb90fd8d4cc34189c55b707b01771786c17b5a8a637a741797ea4c6652ba9204` | `6ae796842f4743d1300f6cdb330bc1249e085e706b81e827c08c81b06df5bd87` |
| 4 | HEAD · `Turing.xr_firstArrival` | 906 | 907 | `eb145823451328efe88abe61aaac6a7105b48eaeee87810c337f3aba141bc8cf` | `d841ef095488ffc47c46302dbc7655bc501c06e05f3ba51694950bdb7a525667` |
| 5 | BASE · `Turing.xr_firstArrival'` | 1353 | 1354 | `0a9a6207f639899176f52469684724f268f086be7713beff852fbf6d70d82a04` | `201bfcf217d62ee8734965615f41bd2068b13c369c07450db2d4bd4a49b96ce0` |
| 6 | HEAD · `Turing.xr_firstArrival'` | 967 | 968 | `e28b9f717952e31144a6d99420763834b19c8e782e7e05ca4d6a0dafb3f57fb2` | `6264f9161c0c7ccd2160c188f2b6ff6895415a00a50745a0dc00f700879c6db9` |
| 7 | BASE · `Complexity.clBank_first` | 1915 | 1916 | `21697ca4b159f24e961397ee14528c153db1c1c24cfdbe764cc380156d122188` | `ee3621d1da13253d9a1a9213eb98964407b2009568fdf0ee1ced7dec522ae21b` |
| 8 | HEAD · `Complexity.clBank_first` | 1700 | 1701 | `519dc220d08c06b321cd197e535ab02b370652b6a2c699f351b411dfabd328fb` | `c52b5d65872504797c241a90718862cdd30ba6a243c0fede76e5c6c84e7579fb` |
| 9 | BASE · `Complexity.clCopy_first` | 2064 | 2065 | `baf384b5f5c9e60c96b811ba06ff67cce333990b27d23eefe0eacf3d9186a2fb` | `f21af73ba269909bd175a1e6c25377c1d2052c20ca7343e38a2ae53e3bac2d5b` |
| 10 | HEAD · `Complexity.clCopy_first` | 1542 | 1543 | `6243508f991d0580e4cdd02bd6a962538b9d74f178229249637a37b3ffd736bd` | `6f3c35378f06668ac60bce1f35b6cdb979b6bb6b4c21d56231ef53154603e29d` |
| 11 | BASE · `Complexity.clRow_first` | 2073 | 2074 | `a24847fa77ceada11ace4dd75c29211ece7386733bde30f8566f0adbcc9c90a8` | `ce657491dab1bfcb0b045fab286d6260fb71ccbed5cde60224f786e83641ef36` |
| 12 | HEAD · `Complexity.clRow_first` | 1664 | 1665 | `4546105fe84b191278be308e9bd258e3b94d34182ad221975f718bcf4d0c1072` | `13c8aea27c6e45e4db6ea90f1375cc90037ed2e06a445a99f878bb4543537094` |
| 13 | BASE · `Complexity.clCmp_first` | 3009 | 3010 | `122d5439fcd90b85a4665f88a7cd6f0715384bbc64e81f8243c0f65eef8c81ff` | `f24cbae9b8c24175272c5160d787406e7ce2a815863d29298ae1b335cc9db4c4` |
| 14 | HEAD · `Complexity.clCmp_first` | 1727 | 1728 | `de21be3a735bee39bdde52c3a20f6cd7978f24b730a47f6b76c46690d08caa67` | `7e7bb011f9a851bcc7eebe4175d1b1b4cbc4d9c91f5168fc93d4c8367b17373c` |
| 15 | BASE · `Complexity.clFirst` | 1511 | 1512 | `626941ec9b5d1cf6d0e7a381b5997e0856f67c6d00a1de311839066b01f9cc2a` | `86b2ac64a0534b3a62153f1ccd3b3c892b11bceb654ad92bd3d95ce10a493423` |
| 16 | HEAD · `Complexity.clFirst` | 1215 | 1216 | `e532c6a70fcec144ed73a11ec5ebdb70c3c0a5085dd2b43a38e8ac8bd4051e5b` | `6ff5db461c14b13f656bbd32c979ce49c9606f3ab25063e89f9c434ee0f9aef4` |
| 17 | BASE · `Turing.inputSeekRewind_run` | 2099 | 2100 | `f1fd86235f1a4db4ceb5ddaf5230383b1d727fc7442db0ea754b6e4063c7c814` | `c5918a7aa02bd686e5116b1ae73829b846efccf5ee629448c61715c4f49413a4` |
| 18 | HEAD · `Turing.inputSeekRewind_run` | 2052 | 2053 | `c6e8804a27a064e97e7c2726a2ae2ed557d7269ba31fd28ce54aa2edc9772b9e` | `21c3e95f0954dd519e1ddeb002e5c0fb0ba7a3e37b5634abc2977c8cbe7cc153` |

`bindings18.json` supplies all exact commits, source/Git blobs, paths, ranges,
manifest identities and per-row assertions. Input manifest SHA256:
`1a0586d32d6bd4f9925a062ca2b4e8aad49ca369152790e615169cc942386d16`. No source or frozen input was altered;
no Lean, screen, mathematical or gate-clearance result is newly claimed.
