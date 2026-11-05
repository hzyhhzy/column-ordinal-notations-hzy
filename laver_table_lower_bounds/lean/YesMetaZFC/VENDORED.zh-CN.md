# 数值 BM4 来源说明 · [English](VENDORED.md)

`BMS/` 中八个文件来自 [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean)。检查时本地副本的 HEAD 为 `bae7e3d741f24a56d80da9b99c1345562cd10c2d`。以下文件哈希固定实际读取的工作树内容；不能只凭 HEAD 推断工作树未修改。

发布时仅把换行规范化为 LF，定义与证明未改变。复用范围为数值 BM4、矩形／规范数组、父指针／祖先、展开及 Hunter Lemma 2.5。未导入上游抽象良序或集合论模型接口；每个依赖都由 Lean 4.33.1 重新编译。来源及版本记录不产生新的上游许可证授权。

见[完整来源清单](../PROVENANCE.json)与[形式化范围](../README.zh-CN.md)。

| File / 文件 | Original SHA-256 | Package SHA-256 (LF) |
|---|---|---|
| Ancestor.lean | ac86e479425ae762801d7718ad759604afc2c336f5313455fef907706420814a | a17a1c64094594c635358b1d7485f048fe0722d35a76f12ed7765da1afa7189e |
| Array.lean | bd0bf713c65529d590dd5313e7924b62691395a9f8760aeb1441b08cc505a03e | 22089646061b7dadfe73e0e1d2914ce971266e99d9a739cd35f3aa16c19cabe6 |
| Decomposition.lean | 1e1305af32bae00f4e3f46ae109e68ed2f9dd495ed40fb8df0589e91a200e0fc | 2d1e1dd7152eca4e89db916e770e4fd337c81af65cc57ad0fcf819142f892fd4 |
| Expansion.lean | ccab24a96c2a814e54be477f86ca6617e8ad2fd31ed7c135956b741d147c8532 | 407ddedcba505d957b66e25ab01ecffae42c92f6ec3648ea33a081080c97d89d |
| Generation.lean | 1c929a98643b5b94027777b149937195f24c363cd74d42fc699b0fa2dbea19e4 | 4a9d14f8611a4fe2a73615851fce3d9b911ec2604ac4693927a5f167e64f9575 |
| Lemma25.lean | 084f0c368e9b53c8df7d6de8935cd67e782aa902f9c7b18f9f2dec35198dfb4f | 12e5f2963502cb9b3c4bb4b9bb49a117a7996b7dfc99fb46f860d3d0e4bf4db4 |
| Parent.lean | 4c640abf4ab691ed66d843bdd519a72157ff12ca59b197a60fffa0cce1e23370 | 21e99ddac5f5467e6242245be48e945f2517557b75a6c3671c1f9e10fd8013fc |
| Reference.lean | c192038a218c940b0e7213683611cf34e914acfc8c45c2102ff27df269db377b | d11bf85cae9a5f9dfe95f748f05b352fb298db58ab2c63f7cd53d02cba4abf15 |
