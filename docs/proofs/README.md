# Causal Atlas Engine：第一轮证明审核稿

日期：2026-11-01。状态：**待作者审核；全篇 Lean 形式化仍在进行中。**

本轮覆盖原稿所有 10 个编号证明对象：Theorems 5.1–5.5、Corollaries 5.1–5.2、Proposition 5.1、Lemmas A.1–A.2。每个对象均提供书面证明或指出原命题为何不成立，并给可证明的修正版。书面证明已经覆盖全部对象；机器证明覆盖范围较窄，逐项见下表。

## 1. 阅读顺序

1. 先审核本页第 2 节的数学修改，这些会改变论文应当声称的结论。
2. 阅读[统计证明](01-statistical-proofs.md)、[支持集与下界](02-support-and-lower-bounds.md)、[桥接选择](03-bridge-selection.md)。每篇都给出假设、逐步推导和边界。
3. 对照第 3 节，打开实际 Lean 声明及[验证记录](../../verification/verification.json)。同一书面命题可能对应多个 Lean 子结论，不能用声明数量代替全篇完成度。

原稿：本地 `07/main_direction_Causal_ATLAS_7papers.pdf`，22 页。

SHA-256：`4f6bcb8ebf0eba8a6a8e0c2d9e5ae9a1e5aff80cbb92ecd24f754153c730501f`。

## 2. 需要作者审核的实质修改

### 2.1 真实方差与次高斯参数分开

真实条件方差记为 $v_i$，MGF 上界参数记为 $s_i^2$。集中不等式使用 $\sum_i w_i^2s_i^2$，方差公式使用 $\sum_i w_i^2v_i$。一个有效的真实方差上界不自动是有效的 MGF 参数。指数尾界还需要全体误差的条件独立或另行证明联合 MGF 界。

### 2.2 曲率误差必须包含校准集

令 $B=(X_J^\top W_JX_J)^{-1}X_J^\top W_J$，$h=B^\top r$。完整曲率偏差为

$$b_{\mathrm{curv}}=\sum_{i\in C}\alpha_i\zeta_i+\sum_{j\in J}h_j\zeta_j-\zeta_*.$$

原稿只约束了第一项与目标余项之差。统计证明第 5 节给出无噪声反例：原半径为零，但校准集曲率仍产生非零偏差。因此原 Corollary 5.1 不能按原样证明。

### 2.3 抽取误差必须包含校准设计与校准效应

实际输入应区分理想研究记录 $Y_i^0$ 与抽取扰动 $\delta_i$。使用实际校准影响权重 $\widehat h$，有效抽取半径可取

$$
B_{\mathrm{ext}}=\widehat L\!\left(u_*+\sum_C\alpha_i u_i+\sum_J|\widehat h_j|u_j\right)
+\sum_C\alpha_i v_i^{\mathrm{ext}}+\sum_J|\widehat h_j|v_j^{\mathrm{ext}}.
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
| Lemma A.1 | [Estimation](../../formal/Atlas/Estimation.lean)：独立加权和的真实 MGF 结论 `weighted_subgaussian`、双侧概率尾界 `subgaussian_two_sided` | 随机条件信息/正则条件分布的整体提升；平方根置信半径及零参数分支的统一包装 |
| Theorem 5.1 | [Algebra](../../formal/Atlas/Algebra.lean)：特征再现推出仿射信号再现；[Estimation](../../formal/Atlas/Estimation.lean)：真实积分期望、无偏性、真实方差和 MGF | 从加权回归逆矩阵推出再现权重；协方差矩阵公式、谱界及条件概率包装 |
| Corollary 5.1 | `full_error_decomposition` 包含所有合并权重的曲率；`interval_inflation` 验证完整余项的确定性区间膨胀 | 从曲率/Hessian 假设推导可计算证书，并与概率尾界组合成同一正式区间定理 |
| Proposition 5.1 | `weighted_error_bound` 验证有符号校准权重必须使用绝对值；误差分解与区间膨胀 | 向量几何范数界、实际矩阵再现、完整 E4–E11 的端到端组合；原式 (5) 已给反例 |
| Theorem 5.2 | [Selection](../../formal/Atlas/Selection.lean)：固定有限族的测度并集界、共同证书失败预算、任意选择、同目标冲突检验、覆盖补集，均完整验证 | 每个候选区间由实际抽取算法产生并满足所输入尾界的端到端证明；随机候选族的条件化版本 |
| Theorem 5.3 | [Asymptotics](../../formal/Atlas/Asymptotics.lean)：固定报告、零均值、单位二阶矩的 iid CLT | 一般条件三角阵 CLT、抽取/曲率余项 Slutsky 步骤、学生化、方差估计一致性及覆盖映射 |
| Corollary 5.2 | 书面证明已完成；无独立完整 Lean 定理 | 逆方差最优性、Gaussian 分位数区间与额外支持约束的正式证明 |
| Theorem 5.4(a) | 完整书面两点测试证明及常数推导 | 高斯测度 KL、测试不等式和统计极小极大风险的 Lean 形式化 |
| Theorem 5.4(b) | [LowerBounds](../../formal/Atlas/LowerBounds.lean)：距离函数及其负函数的 Lipschitz 性、观测不可区分性、任意确定性估计量的绝对误差下界；平方损失恒等式 | 对随机化估计量的风险积分及显式 inf/sup 表述；书面证明已覆盖 |
| Theorem 5.5 | [Bridge](../../formal/Atlas/Bridge.lean)：$2\varepsilon$ 单步误差、弱次模进展、递推、指数界和集合序列相对任意预算内比较集的保证 | 有限候选 argmax 的算法构造、将统一估计事件自动装配为每步条件、具体直径目标满足弱次模性的模型证明 |
| Lemma A.2 | [Support](../../formal/Atlas/Support.lean)：任意有限非空索引、实赋范空间中，支持残差在 simplex 上取得最小值，完整验证 | 若实际算法加稳定性约束，需要另证新可行域非空且闭 |

5.4 拆成两行，因此表格有 11 行而原编号证明对象为 10 个。

### 5.5 的已验证加强界

Lean 对满足条件的序列证明

$$F(S_B)\ge (1-e^{-\gamma})F(T)-2B\varepsilon,\qquad |T|\le B.$$

这是用 $\sum_{j=0}^{B-1}q^j\le B$ 得到的界；当 $0<\gamma\le1$ 时，它强于原稿的误差项 $2B\varepsilon/\gamma$。取 $T$ 为最优比较集即得相应 oracle 界。有限候选最优集的存在和估计贪心规则到单步假设的装配目前在书面层给出，未作为最终 Lean 声明的算法构造。

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

验证脚本逐文件生成本项目 `.olean`，编译总入口，再对每个已声明定理执行 `#print axioms`。日志、退出码、声明列表、文件 SHA-256 及标准内核公理依赖写入 [verification](../../verification)。只允许 `propext`、`Classical.choice`、`Quot.sound`；不允许 `sorryAx` 或自定义未证明公理。

Mathlib 标准库依赖可在锁定版本查看：[次高斯工具](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Probability/Moments/SubGaussian.lean)、[CLT](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Probability/CentralLimitTheorem.lean)。调用库中已经证明的定理属于内核验证；把目标结论写成新的假设则不构成该结论的证明。

## 5. 后续形式化顺序

1. 补齐回归矩阵与合并影响权重的连接、谱界，统一固定报告的有限样本定理。
2. 将抽取设计扰动、曲率证书与区间覆盖合并，接入已验证的选择层。
3. 完成经典逆方差特例，以及 5.4(a) 的高斯两点风险证明。
4. 将条件三角阵 CLT、Slutsky、学生化和方差一致性逐步形式化。

在这些项目完成前，不能将本轮记录描述为“文章所有定理均已通过 Lean”。
