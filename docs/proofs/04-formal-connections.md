# 第二轮：将回归、误差证书与统计结论连接起来

更新日期：2026-11-03。本文件解释本轮新增的机器证明及其数学推导。它补充前三份证明文档；原稿的实质修正仍需作者审核。精确形式化范围见[完成度总览](README.md)，实际编译结果见[验证记录](../../verification/verification.json)。

## 1. 从回归逆矩阵到实际估计量无偏

对应 [Regression.lean](../../formal/Atlas/Regression.lean)。令校准设计为 $`X`$，源设计为 $`S`$，权矩阵为 $`W`$。所有索引集有限，Gram 矩阵 $`G=X^{\top}WX`$ 的行列式非零。此处代数恒等式不要求 $`W`$ 对称正定；统计效率或谱界需要更强条件。

定义

$$
B=G^{-1}X^{\top}W,\qquad r=x_{\ast}-S^{\top}a,\qquad h=B^{\top}r.
$$

由逆矩阵恒等式直接得到 $`BX=I`$，继而

$$
X^{\top}h=(BX)^{\top}r=r,\qquad S^{\top}a+X^{\top}h=x_{\ast}.
$$

因此对任意参数向量 $`\beta`$，

$$
a^{\top}S\beta+h^{\top}X\beta=x_{\ast}^{\top}\beta.
$$

实际回归修正还满足 $`r^{\top}BY_J=h^{\top}Y_J`$。若每条观测可积，且 $`\mathbb E Y_C=S\beta`$、$`\mathbb E Y_J=X\beta`$，有限和的积分线性给出

$$
\mathbb E\bigl[a^{\top}Y_C+r^{\top}BY_J\bigr]=a^{\top}S\beta+h^{\top}X\beta=x_{\ast}^{\top}\beta.
$$

`calibrated_estimator_unbiased` 的输入是矩阵可逆、可积性和均值模型；特征再现由此前的矩阵证明推出。该期望结论本身不需要独立性。这里的设计和权重固定；随机设计下的条件概率版本仍需另行构造。

## 2. 完整抽取误差证书

对应 [Extraction.lean](../../formal/Atlas/Extraction.lean)。把源记录与校准记录合并为有限索引集，使用真实的有符号权重 $`a_i`$。在实内积空间中，设真实特征为 $`x_i`$，抽取特征为 $`\widehat x_i`$，并有

$$
\|x_i-\widehat x_i\|\le u_i,\qquad \|\beta\|\le L,\qquad |\delta_i|\le v_i.
$$

由 Cauchy–Schwarz 不等式，

$$
|\langle x_i-\widehat x_i,\beta\rangle|\le\|x_i-\widehat x_i\|\,\|\beta\|\le Lu_i.
$$

三角不等式于是给出单条记录的误差界 $`|\langle x_i-\widehat x_i,\beta\rangle+\delta_i|\le Lu_i+v_i`$。对合并权重求和后，完整抽取半径为

$$
B_{\mathrm{ext}}=L u_{\ast}+\sum_i |a_i|(Lu_i+v_i).
$$

这里 $`u_{\ast}`$ 是目标特征误差，源与校准的设计误差、效应抽取误差全部计入。若抽取特征满足 $`\sum_i a_i\widehat x_i=\widehat x_{\ast}`$，则真实特征的残差恰好由这些扰动构成。把完整曲率证书 $`B_{\mathrm{curv}}`$ 加入，得到

$$
|\widehat\theta-\theta_{\ast}-N|\le B_{\mathrm{ext}}+B_{\mathrm{curv}}.
$$

本模块分别验证向量扰动、标量内积、单项误差、加权求和、抽取设计误差分解及最终证书。这里的 $`L`$ 约束完整参数向量范数；如果论文只约束斜率部分，必须先消去无误差的截距坐标，再使用该界。它要求所输入的误差证书成立；证书如何由实际抽取系统可靠地产生，仍属于需要验证的模型与实现部分。将抽象有限索引和内积具体实例化为源／校准矩阵，是仍需完成的连接。

## 3. 从 MGF 到完整区间及任意后续选择

对应 [Confidence.lean](../../formal/Atlas/Confidence.lean)。若噪声 $`N`$ 具有次高斯 MGF 参数 $`c\ge0`$，令 $`0<\eta<1`$，定义

$$
r(c,\eta)=\sqrt{2c\log(2/\eta)}.
$$

当 $`c>0`$ 时，双侧 Chernoff 界和恒等式

$$
2\exp\!\left(-\frac{r(c,\eta)^2}{2c}\right)=\eta
$$

推出 $`\mathbb P(|N|>r(c,\eta))\le\eta`$。当 $`c=0`$ 时，MGF 条件推出 $`N=0`$ 几乎处处，所以零半径同样有效。这个分支由 `confidence_tail_zero` 单独验证，统一结论为 `confidence_tail`。

设共同证书事件为 $`E`$，$`\mathbb P(E^c)\le\rho`$，且在 $`E`$ 上有完整余项界 $`|\widehat\theta-\theta_{\ast}-N|\le R`$。半径 $`R`$ 可以依赖数据。三角不等式给出事件包含关系

$$
\{|\widehat\theta-\theta_{\ast}|>r(c,\eta)+R\}\subseteq\{|N|>r(c,\eta)\}\cup E^c.
$$

因而 `certified_interval_failure_le` 得到失败概率至多 $`\eta+\rho`$。对于独立的有限误差族，`weighted_complete_interval_failure_le` 进一步直接从各项 MGF 条件出发，使用

$$
N=\sum_i a_i\varepsilon_i,\qquad c=\sum_i a_i^2c_i,\qquad R=B_{\mathrm{curv}}+\sum_i|a_i|b_i,
$$

证明包含全部源与校准曲率、抽取误差的区间。其中曲率证书必须约束 $`|\sum_i a_i\zeta_i-\zeta_{\ast}|`$，不能遗漏校准项。

对预先固定的有限候选族 $`\mathcal R`$，每个候选有自己的 $`(c_r,\eta_r,R_r)`$，共用证书事件 $`E`$。把各候选的噪声尾事件取并集，得到

$$
\mathbb P\bigl(\text{至少一个候选区间失效}\bigr)\le\sum_{r\in\mathcal R}\eta_r+\rho.
$$

共同证书失败概率只出现一次。任意依赖数据的选择规则和输出事件的联合失败事件，均包含于上述并集，因此 `selected_certified_interval_failure_le` 具有同样的上界。该结论不声称条件于“系统输出了某个报告”的条件覆盖率，也不允许把数据选出的单个候选当成预先固定的候选族。

## 4. 逆方差权重的最优性与唯一性

对应 [InverseVariance.lean](../../formal/Atlas/InverseVariance.lean)。有限索引集非空，每项方差 $`v_i>0`$。设

$$
P=\sum_i v_i^{-1},\qquad a_i^{\ast}=\frac{v_i^{-1}}P,\qquad V(a)=\sum_i v_i a_i^2.
$$

首先 $`P>0`$，每个 $`a_i^{\ast}>0`$，且 $`\sum_i a_i^{\ast}=1`$。对任意归一化实权重 $`\sum_i a_i=1`$，逐项展开平方并求和：

$$
\sum_i v_i(a_i-a_i^{\ast})^2=\sum_i v_i a_i^2-\frac2P\sum_i a_i+\frac1{P^2}\sum_i v_i^{-1}=V(a)-P^{-1}.
$$

故

$$
V(a)=P^{-1}+\sum_i v_i(a_i-a_i^{\ast})^2\ge P^{-1}=V(a^{\ast}).
$$

若等号成立，每项非负平方项之和为零。由 $`v_i>0`$ 得 $`a_i=a_i^{\ast}`$ 对所有 $`i`$ 成立；反向显然。因此最优解唯一。这一结论允许比较权重为负，比仅在 simplex 上最优化更强。

形式化没有声称逆方差权重自动满足额外的因果支持约束。高斯分位数区间也不是上述二次优化的推论，其概率分布与分位数步骤仍需独立完成。

## 5. 随机化估计量的未观测目标下界

对应 [Risk.lean](../../formal/Atlas/Risk.lean)。令 $`Z`$ 是概率空间上的平方可积随机输出。对任意实数 $`a`$，逐点有

$$
(Z-a)^2+(Z+a)^2=2Z^2+2a^2\ge2a^2.
$$

平方可积保证两项损失可积。积分并用最大值不小于平均值，得到

$$
\max\{\mathbb E(Z-a)^2,\mathbb E(Z+a)^2\}\ge a^2.
$$

现令源特征集合为 $`S=\{m_i\}`$，$`d=\operatorname{dist}(m_{\ast},S)`$，取

$$
f_{+}(m)=L\operatorname{dist}(m,S),\qquad f_{-}(m)=-L\operatorname{dist}(m,S).
$$

前一轮已证明二者为 $`L`$-Lipschitz，且全部源观测均为零。在目标点的取值为 $`\pm Ld`$。任意使用同一随机种子分布的估计量在这两个世界中产生相同的输出 $`Z=T(0,U)`$。取 $`a=Ld`$，至少一个世界的平方风险不小于 $`L^2d^2`$。

`randomized_unsupported_target_lower_bound` 对任意这样的估计映射构造一个反例世界，包含 Lipschitz 性、源点一致性和风险积分下界。当前实值积分版本明确要求 $`T(0,U)`$ 平方可积；允许无限风险的扩展非负积分，以及显式下确界／上确界包装，尚未纳入该声明。

## 6. 余项、方差一致性与学生化

对应 [Asymptotics.lean](../../formal/Atlas/Asymptotics.lean)。若已经建立 $`X_n\Rightarrow Z`$，且归一化余项 $`R_n\to_p0`$，Slutsky 定理给出 $`X_n+R_n\Rightarrow Z`$。本模块还直接证明：如果 $`g`$ 在常数 $`c`$ 连续、$`Q_n\to_p c`$，则 $`g(Q_n)\to_p g(c)`$。证明用连续性的局部定义，把变换后超出任意阈值的事件包含于变换前的偏离事件。

取 $`g(q)=(\sqrt q)^{-1}`$，该函数在 $`q=1`$ 连续。于是相对方差 $`Q_n=\widehat V_n/V_n\to_p1`$ 推出 $`g(Q_n)\to_p1`$，再由 Slutsky 得

$$
\frac{X_n+R_n}{\sqrt{Q_n}}\Rightarrow Z.
$$

`studentized_limit` 不要求主项、余项与方差估计量独立。这里已经成立的主项极限是明确前提，不能用此定理替代证明一般三角阵中心极限定理。Lean 中逆平方根在非正数处有总定义；由于只使用其在 1 处的连续性，这不需要对所有有限样本强加 $`Q_n>0`$。若实际统计量要求处处可除，应另加正方差条件。

为避免直接假设聚合方差的一致性，本轮进一步证明充分条件。令 $`V_n=\sum_i w_{ni}^2v_{ni}>0`$，则

$$
\left|\frac{\widehat V_n}{V_n}-1\right|\le\frac{\sum_i w_{ni}^2|\widehat v_{ni}-v_{ni}|}{V_n}.
$$

若右侧依概率收敛于零，则左侧也依概率收敛于零。因此 `variance_consistent_of_weighted_errors` 从分量误差条件推出相对方差一致性，允许权重随机、各方差估计量相关。具体方差估计方法是否满足右侧条件，仍须另证。

## 7. 有限贪心构造与概率保证

对应 [BridgeAlgorithm.lean](../../formal/Atlas/BridgeAlgorithm.lean)。有限非空集合上的实值分数必然取得最大值，据此定义每步在尚未选入的候选中选择估计增益最大者。候选耗尽后使用一个已在候选集内的固定元素，不再增大集合。归纳给出所构造集合始终属于候选全集，且第 $`k`$ 步的基数至多为 $`k`$。

如果所选元素 $`u`$ 和任一候选 $`v`$ 的估计增益误差都不超过 $`\varepsilon`$，则

$$
\Delta(v\mid S)\le\widehat\Delta(v\mid S)+\varepsilon\le\widehat\Delta(u\mid S)+\varepsilon\le\Delta(u\mid S)+2\varepsilon.
$$

`nextChoice_approximate` 将真实构造接入前一轮的弱次模递推。因此对任意候选全集内、基数不超过 $`B`$ 的比较集 $`T`$，当 $`B>0`$、$`0\le\gamma\le1`$、$`\varepsilon\ge0`$，且 $`F`$ 单调、具有相应弱次模性、$`F(\varnothing)=0`$ 时，

$$
F(S_B)\ge(1-e^{-\gamma})F(T)-2B\varepsilon.
$$

有限全集的可行子集族非空且有限，故 `budget_optimum_exists` 证明最优比较集存在。统一增益误差若在一个失败概率至多为 $`\rho`$ 的事件上成立，`constructed_greedy_failure_le` 给出上述算法保证的失败概率至多为 $`\rho`$，不再把逐步近似贪心性质当作独立输入。

这里构造的是选择规则的数学规格，使用存在性选择；并未验证引擎的可执行实现、具体增益估计器的误差率，或实际直径缩减目标的弱次模性。一般条件三角阵中心极限定理与高斯两点统计风险下界也仍在剩余清单内。
