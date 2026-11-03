# Causal Atlas Engine

研究材料与形式化证明工作区。

当前交付是**第二轮证明审核稿（2026-11-03）**：新增回归与无偏性、完整误差区间、逆方差最优性、学生化、随机化下界和有限贪心构造。全部编号命题均有书面证明或修正说明，Lean 覆盖范围逐项列明，**尚未完成全篇端到端形式化**。

- [从这里审核：证明总览、修改要点与完成度](docs/proofs/README.md)
- [统计定理的逐步证明与反例](docs/proofs/01-statistical-proofs.md)
- [支持权重、经典特例与误差下界](docs/proofs/02-support-and-lower-bounds.md)
- [桥接实验选择](docs/proofs/03-bridge-selection.md)
- [第二轮新增证明：从矩阵和误差证书到统计结论](docs/proofs/04-formal-connections.md)
- [Lean 源码](formal/Atlas)
- [机器验证记录](verification/verification.json)与[原始编译、公理审计日志](verification/lean-verification.log)

此稿供作者审核，不能将修正后的假设或已验证的子命题直接描述为原稿所有定理均已获 Lean 证明。
