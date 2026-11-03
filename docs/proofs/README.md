# Causal Atlas Engine：第二轮证明审核稿

日期：2026-11-03。状态：**待作者审核；全篇 Lean 形式化仍在进行中。**

本轮共有 **90 个 Lean 定理／引理声明**通过编译和公理审计，较第一轮增加 58 个。该数量是形式化声明数，不代表原稿完成比例。文档公式与版式的检查记录见[Markdown 验证报告](../../verification/markdown-verification.json)。

本轮覆盖原稿所有 10 个编号证明对象：Theorems 5.1–5.5、Corollaries 5.1–5.2、Proposition 5.1、Lemmas A.1–A.2。每个对象均提供书面证明或指出原命题为何不成立，并给可证明的修正版。书面证明已经覆盖全部对象；机器证明覆盖范围较窄，逐项见下表。

本轮新增内容集中在[矩阵、完整证书与统计结论的连接证明](04-formal-connections.md)。

## 1. 阅读顺序

1. 先审核本页第 2 节的数学修改，这些会改变论文应当声称的结论。
2. 阅读[统计证明](01-statistical-proofs.md)、[支持集与下界](02-support-and-lower-bounds.md)、[桥接选择](03-bridge-selection.md)。每篇都给出假设、逐步推导和边界。
3. 对照第 3 节，打开实际 Lean 声明及[验证记录](../../verification/verification.json)。同一书面命题可能对应多个 Lean 子结论，不能用声明数量代替全篇完成度。

原稿：本地 `07/main_direction_Causal_ATLAS_7papers.pdf`，22 页。

SHA-256：`4f6bcb8ebf0eba8a6a8e0c2d9e5ae9a1e5aff80cbb92ecd24f754153c730501f`。

## 2. 需要作者审核的实质修改

### 2.1 真实方差与次高斯参数分开

真实条件方差记为 $`v_i`$，MGF 上界参数记为 $`s_i^2`$。集中不等式使用 $`\sum_i w_i^2s_i^2`$，方差公式使用 $`\sum_i w_i^2v_i`$。一个有效的真实方差上界不自动是有效的 MGF 参数。指数尾界还需要全体误差的条件独立或另行证明联合 MGF 界。

### 2.2 曲率误差必须包含校准集

令 $`B=(X_J^\top W_JX_J)^{-1}X_J^\top W_J`$，$`h=B^\top r`$。完整曲率偏差为

$$
b_{\mathrm{curv}}=\sum_{i\in C}\alpha_i\zeta_i+\sum_{j\in J}h_j\zeta_j-\zeta_{\ast}.
$$

原稿只约束了第一项与目标余项之差。统计证明第 5 节给出无噪声反例：原半径为零，但校准集曲率仍产生非零偏差。因此原 Corollary 5.1 不能按原样证明。

### 2.3 抽取误差必须包含校准设计与校准效应

实际输入应区分理想研究记录 $`Y_i^0`$ 与抽取扰动 $`\delta_i`$。使用实际校准影响权重 $`\widehat h`$，有效抽取半径可取

$$
B_{\mathrm{ext}}=\widehat L\!\left(u_{\ast}+\sum_C\alpha_i u_i+\sum_J|\widehat h_j|u_j\right) +\sum_C\alpha_i v_i^{\mathrm{ext}}+\sum_J|\widehat h_j|v_j^{\mathrm{ext}}.
$$

这要求实际抽取矩阵可逆、特征再现恒等式成立、各证书同时有效，并保持研究误差在所用条件信息下的统计性质。参数范数、曲率和噪声参数证书的失败概率都应进入总预算。详见统计证明第 6 节。

### 2.4 选择有效性与冲突报告

固定有限族的同时覆盖可以保护任意后续报告选择；一个由数据挑出的单元素集合不能冒充预先固定的有限族。若两个区间针对同一真值，则它们不相交意味着至少一个区间失效。因此 reconcile 应解释为对“共同目标及所用模型同时成立”的检验，而非在所有区间有效的同一事件上还出现冲突。Lean 证明的是联合失败概率控制，不是条件于输出 link 后的条件覆盖率。

### 2.5 渐近结论需要缩小范围

同一数据上选择绝对标准化误差最大的报告，即使每个候选都精确正态，选择后也不再正态。5.3R 的书面证明明确要求选择后仍成立的条件独立、条件 Lindeberg 条件和可忽略完整余项。方差一致性是需要另证的条件；扩张非可忽略半径只能保证覆盖下界，不能声称精确覆盖。

### 2.6 下界与桥接条件

5.4(b) 中到观测点集的距离不同于支持诊断中到凸包的距离。逆方差权重也未必满足额外的精确支持约束。5.5 的单调性和弱次模性是额外假设，不会由“预期区间直径缩减”的定义自动推出。

## 3. 原命题与 Lean 的准确对应

下表中的“已验证”仅指所链接 Lean 文件中的精确声明。所有交付的 Lean 声明均须通过内核检查；未完成的数学内容放在本表，而不以 `sorry` 或新增公理隐藏。

| 原编号 | 本轮 Lean 已覆盖 | 尚未覆盖的部分 |
|---|---|---|
| Lemma A.1 | [Estimation](../../formal/Atlas/Estimation.lean)：独立加权和 MGF 与双侧尾界；[Confidence](../../formal/Atlas/Confidence.lean)：平方根半径、正参数与零参数分支 | 随机条件信息／正则条件分布的整体提升 |
| Theorem 5.1 | [Regression](../../formal/Atlas/Regression.lean)：从 Gram 可逆推出实际校准权重再现和回归估计量无偏；[Estimation](../../formal/Atlas/Estimation.lean)：加权方差与 MGF | 协方差矩阵公式、谱界；实际回归表达式与所有统计结论的统一包装；随机设计的条件概率版本 |
| Corollary 5.1 | [Confidence](../../formal/Atlas/Confidence.lean)：完整曲率／抽取余项、独立加权噪声、明确置信半径和证书失败预算的组合区间定理 | 从曲率／Hessian 条件推导可计算的完整曲率证书 |
| Proposition 5.1 | [Extraction](../../formal/Atlas/Extraction.lean)：向量扰动、内积误差、有符号权重汇总、目标误差及完整抽取证书；矩阵再现与概率区间分别已验证 | 将有限索引和内积表示具体连接到源／校准矩阵及 E4–E11 的统一定理；实际抽取证书产生机制与随机设计有效性 |
| Theorem 5.2 | [Selection](../../formal/Atlas/Selection.lean) 与 [Confidence](../../formal/Atlas/Confidence.lean)：固定有限族、明确半径、共同证书只计一次、任意后续选择、同目标冲突检验和覆盖补集 | 实际抽取算法产生有效证书的端到端证明；随机候选族的条件化版本 |
| Theorem 5.3 | [Asymptotics](../../formal/Atlas/Asymptotics.lean)：固定 iid CLT、余项 Slutsky、局部连续映射、逆平方根一致性、学生化、加权分量误差推出聚合方差一致性 | 一般条件三角阵 CLT；具体方差估计方法满足误差条件；正态分位数到覆盖率的正式映射 |
| Corollary 5.2 | [InverseVariance](../../formal/Atlas/InverseVariance.lean)：逆方差权重正性、归一化、完整配方恒等式、全体归一化实权重中的最优性与唯一性 | Gaussian 分位数区间与额外支持约束的正式证明 |
| Theorem 5.4(a) | 完整书面两点测试证明及常数推导 | 高斯测度 KL、测试不等式和统计极小极大风险的 Lean 形式化 |
| Theorem 5.4(b) | [LowerBounds](../../formal/Atlas/LowerBounds.lean) 与 [Risk](../../formal/Atlas/Risk.lean)：Lipschitz 不可区分世界、确定性绝对误差下界、平方可积随机化估计量的真实风险积分下界 | 允许无限风险的扩展积分和显式 inf/sup 表述 |
| Theorem 5.5 | [Bridge](../../formal/Atlas/Bridge.lean) 与 [BridgeAlgorithm](../../formal/Atlas/BridgeAlgorithm.lean)：有限 argmax、集合递归构造、候选集及预算约束、最优比较集存在、统一误差事件到算法概率保证 | 具体直径目标满足弱次模性；具体增益估计器的统一误差率；引擎可执行实现与数学选择规格的一致性 |
| Lemma A.2 | [Support](../../formal/Atlas/Support.lean)：任意有限非空索引、实赋范空间中，支持残差在 simplex 上取得最小值 | 若实际算法加稳定性约束，需要另证新可行域非空且闭 |

5.4 拆成两行，因此表格有 11 行而原编号证明对象为 10 个。

### 5.5 的已验证加强界

Lean 对满足条件的序列证明

$$
F(S_B)\ge (1-e^{-\gamma})F(T)-2B\varepsilon,\qquad |T|\le B.
$$

这是用 $`\sum_{j=0}^{B-1}q^j\le B`$ 得到的界；当 $`0<\gamma\le1`$ 时，它强于原稿的误差项 $`2B\varepsilon/\gamma`$。本轮已证明有限候选最优集存在，并将估计贪心选择的数学构造接入该界；统一误差事件的失败概率也已传递到最终保证。单调性、弱次模性及估计误差证书仍是必须检验的模型前提。

## 4. 验证与复现

固定 Lean `v4.34.0-rc1`；Mathlib 提交 `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`。依赖的确切提交均在 [lake-manifest.json](../../formal/lake-manifest.json)。本机复用了已有同版本依赖缓存，缓存本身不上传仓库。

安装 Lean/elan 和 Python 后，在仓库根目录执行：

```text
cd formal
lake update
lake exe cache get
python verify.py
```

`lakefile.lean` 固定 Mathlib 版本标签，manifest 固定实际提交。严格重现时保留 manifest；若 `lake update` 改变任何提交，应先检查差异而非继续声称使用本轮版本。已还原依赖的环境可直接运行最后两条命令。

验证脚本按本地导入依赖顺序逐文件生成本项目 `.olean`，编译总入口，再对每个已声明定理执行 `#print axioms`。日志、退出码、声明列表、文件 SHA-256 及标准内核公理依赖写入 [verification](../../verification)。只允许 `propext`、`Classical.choice`、`Quot.sound`；不允许 `sorryAx` 或自定义未证明公理。

Mathlib 标准库依赖可在锁定版本查看：[次高斯工具](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Probability/Moments/SubGaussian.lean)、[CLT](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Probability/CentralLimitTheorem.lean)。调用库中已经证明的定理属于内核验证；把目标结论写成新的假设则不构成该结论的证明。

## 5. 剩余形式化工作

1. 补齐回归协方差矩阵、谱界，以及实际矩阵与向量抽取证书、统计区间的统一实例化。
2. 从 Hessian 等模型条件推导完整曲率证书，验证实际抽取证书与具体方差估计方法。
3. 完成高斯分位数区间和 5.4(a) 的高斯 KL／两点测试风险证明。
4. 完成一般条件三角阵 CLT、随机设计及随机候选族的条件化，以及渐近覆盖率映射。
5. 扩展 5.4(b) 至无限风险的非负积分；验证具体桥接目标、增益估计器与引擎实现。

这些内容尚未完成，不能将本轮记录描述为“文章所有定理均已通过 Lean”。
