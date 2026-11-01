# Causal Atlas Engine

研究材料与形式化证明工作区。

当前交付是**第一轮证明审核稿**：全部编号命题均有书面证明或修正说明，Lean 只覆盖状态表明确列出的部分，**尚未完成全篇端到端形式化**。

- [从这里审核：证明总览、修改要点与完成度](docs/proofs/README.md)
- [统计定理的逐步证明与反例](docs/proofs/01-statistical-proofs.md)
- [支持权重、经典特例与误差下界](docs/proofs/02-support-and-lower-bounds.md)
- [桥接实验选择](docs/proofs/03-bridge-selection.md)
- [Lean 源码](formal/Atlas)
- [机器验证记录](verification/verification.json)与[原始编译、公理审计日志](verification/lean-verification.log)

此稿供作者审核，不能将修正后的假设或已验证的子命题直接描述为原稿所有定理均已获 Lean 证明。
