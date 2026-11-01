# Statistical theorem audit and corrected proofs

审查对象：`07/main_direction_Causal_ATLAS_7papers.pdf`，22 页版本，重点为 Assumptions 3.1–3.6、Lemma A.1、Theorem 5.1、Corollary 5.1、Proposition 5.1、Theorems 5.2–5.3。

本文件给出数学审查、明确的修正版命题及逐步书面证明。**本文件不是 Lean 验证报告；其中没有任何命题被本文件声明为已经通过 Lean。** 正式稿应逐项采用或拒绝所列修改，不能将修改后的结论直接当作原命题的证明。

## 1. 审查结论与修改清单

| 原位置 | 判断 | 必须修改的内容 |
|---|---|---|
| Lemma A.1，pp.15–16 | 在写明全部条件独立、可测性及零尺度边界后成立 | 随机权重和尺度必须对条件信息可测；使用 MGF 尺度而非任意方差上界 |
| Theorem 5.1，pp.7–9 | 线性去偏恒等式成立；概率部分需澄清/补强条件 | 仿射模型须覆盖 `C ∪ J` 及目标；分开真实方差和 sub-Gaussian proxy；仅两组独立或对角协方差不足以给出所写指数尾界 |
| Corollary 5.1，p.9 | 原结论一般错误 | 漏掉校准集曲率偏差 `rᵀ B_J ζ_J`，必须给完整偏差证书 |
| Proposition 5.1，p.9 | 第一个几何不等式成立；据此声称完整区间有效不成立 | 缺校准集机制抽取误差、校准集效应抽取误差、抽取设计矩阵引起的斜率变化；参数范数置信上界的失败概率必须计入 |
| Theorem 5.2，pp.9–10 | 有效的同时区间可保留任意后续选择；现有前提尚未建立这些区间 | 候选族与错误预算须预先固定或在保持条件有效性的外部信息下可测；有限族本身不足；共同目标下 reconcile 应解释为模型一致性检验 |
| Theorem 5.3，p.10 | 任意数据选择后的常态近似没有得到证明 | 需固定报告、独立选择，或针对选择后条件分布重新假设并证明 CLT；“方差一致性”目前只是前提；非可忽略半径只给保守覆盖下界 |

共同原则：把**代数恒等式**、**统计模型假设**、**抽取误差事件**、**数据选择规则**分别陈述。把某个数据依赖对象写进一个 sigma-field，并不能自动使条件零均值或条件独立成立。

## 2. 统一记号与概率前提

以下各有限样本命题先固定一个报告。设 `C` 与 `J` 为不相交的有限索引集，`C` 非空；`x_i=(1,m_iᵀ)ᵀ ∈ R^{p+1}`，目标特征为 `x_*`。令

$$
\alpha_i\ge0,\qquad \sum_{i\in C}\alpha_i=1,
\qquad
r=x_*-\sum_{i\in C}\alpha_i x_i.
$$

`X` 是以 `x_jᵀ, j∈J` 为行的矩阵，`W` 为对角正定权重矩阵。定义

$$
G=X^\top W X,\qquad B=G^{-1}X^\top W,
\qquad h=B^\top r.
\tag{S1}
$$

假设 `G` 正定，且 `λ_min(G)≥λ>0`、`‖W‖op≤w_max`。`B` 是校准回归的线性算子，`h` 是校准集对最终报告的实际影响权重。注意 `h_j` 可以为负。

令 `𝒢` 为条件信息。集合、特征、权重、目标及下文出现的真实均值和尺度都对 `𝒢` 可测。理想研究效应记录满足

$$
Y_i^0=\tau_i+\varepsilon_i,\qquad
\mathbb E[\varepsilon_i\mid\mathcal G]=0,
\qquad i\in C\cup J.
\tag{S2}
$$

分别记

$$
v_i=\operatorname{Var}(\varepsilon_i\mid\mathcal G),
\qquad
\mathbb E[e^{t\varepsilon_i}\mid\mathcal G]
\le e^{t^2s_i^2/2},\quad t\in\mathbb R.
\tag{S3}
$$

`v_i` 是真实条件方差，`s_i²` 是有效 MGF proxy；一般只有 `v_i≤s_i²`，不能默认相等。为应用独立乘积尾界，明确要求整个有限族 `(ε_i)_{i∈C∪J}` 在给定 `𝒢` 后相互独立。仅要求两组相互独立，不能替代组内条件独立。

对一般条件分布可采用标准 Borel 概率空间上的正则条件分布：下面证明在几乎处处的条件分布上逐点成立。这样对 `𝒢` 可测的随机权重和随机尺度进行代入是严格的。也可用条件期望与有理参数逼近建立同样结论。

“非效应信息”不是零均值条件的证明。若抽取机制、选取研究或确定权重时利用了效应数值，必须单独验证 (S2)–(S3)，或使用与本次推断误差独立的数据做这些操作。

## 3. Lemma A.1 的完整修正版与证明

### A.1R：条件 sub-Gaussian 加权和

设有限族 `(ε_i)` 条件独立并满足 (S2)–(S3)，`a_i` 为 `𝒢` 可测实数。定义

$$
Z=\sum_i a_i\varepsilon_i,
\qquad S^2=\sum_i a_i^2s_i^2.
$$

则对所有实数 `t`，

$$
\mathbb E[e^{tZ}\mid\mathcal G]\le e^{t^2S^2/2}.
\tag{A1}
$$

在 `S²>0` 时，对所有 `u>0` 有

$$
\mathbb P(|Z|\ge u\mid\mathcal G)
\le 2\exp\{-u^2/(2S^2)\}.
\tag{A2}
$$

因此对 `t>0`，

$$
\mathbb P(|Z|>\sqrt{2S^2t}\mid\mathcal G)\le 2e^{-t}.
\tag{A3}
$$

若 `S²=0`，则 `Z=0` 条件几乎处处，(A3) 仍成立。若右边超过 1，可以取它与 1 的最小值。

**证明。** 固定一个满足假设的条件分布。独立性与 MGF 条件给出

$$
\mathbb E e^{tZ}
=\prod_i\mathbb E e^{ta_i\varepsilon_i}
\le\prod_i e^{t^2a_i^2s_i^2/2}
=e^{t^2S^2/2}.
$$

对任意 `λ>0`，Markov 不等式给出

$$
\mathbb P(Z\ge u)
\le e^{-\lambda u}\mathbb E e^{\lambda Z}
\le e^{-\lambda u+\lambda^2S^2/2}.
$$

`S²>0` 时取 `λ=u/S²`，得到上尾 `exp{-u²/(2S²)}`；对 `-Z` 同样推导下尾，再取并集即得 (A2)。代入 `u=√(2S²t)` 得到 (A3)。若 `S²=0`，上式对任意 `λ>0` 给出 `P(Z≥u)≤e^{-λu}`，令 `λ→∞`；下尾同理。对正有理数 `u` 取可数并集即知 `Z=0` 几乎处处。所有论证在条件分布下成立，故得到条件形式。证毕。

### 不能将真实方差直接放进 (A3)

取 `Q∼Bernoulli(0.01)`，`Z=Q−0.01`。其均值为 0，方差为 `0.0099`，且因有界而具有有效 sub-Gaussian proxy。然而若错误地把 proxy 换为真实方差并取 `t=6`，则

$$
\mathbb P(|Z|>\sqrt{2(0.0099)6})=0.01
>2e^{-6}\approx0.004958.
$$

因此“任何真实方差上界都可用于 sub-Gaussian 尾界”一般错误。若原稿将 `σ_i²` 同时假设为真实方差和有效 MGF proxy，那么这是额外的、较强的分布假设，必须明说；不能把它当作普通 sub-Gaussian 性的推论。

### 对角协方差也不够

令 `U` 在三维二元向量空间 `F₂³` 上均匀分布，并对七个非零向量 `a` 定义 `ε_a=(-1)^{a·U}`。这七个变量均为零均值 Rademacher，二阶方差为 1，彼此不相关，单个变量的 MGF proxy 为 1，但并非相互独立。取 `Z=(1/7)Σ_a ε_a`，则 `Z=1` 的概率为 `1/8`，`Z=−1/7` 的概率为 `7/8`，故真实方差为 `1/7`。若错误使用独立和尾界，取 `t=3` 会得到

$$
1/8=\mathbb P(|Z|>\sqrt{6/7})
\le2e^{-3}\approx0.09957<1/8,
$$

矛盾。因而 Theorem 5.1 的指数尾界必须具有全部误差条件独立，或直接的联合 MGF 假设。

## 4. Theorem 5.1：去偏、方差与浓缩

### 5.1R：固定报告、理想特征、精确仿射模型

采用第 2 节条件，并在 **`C∪J` 与目标上使用同一个参数** `β`，满足

$$
\tau_i=x_i^\top\beta\quad(i\in C\cup J),
\qquad \tau_*=x_*^\top\beta.
\tag{T1}
$$

定义

$$
\widehat\beta=BY_J^0,
\quad
\widehat\theta_{\rm raw}=\sum_{i\in C}\alpha_iY_i^0,
\quad
\widehat\theta_{\rm db}
=\sum_{i\in C}\alpha_iY_i^0+r^\top\widehat\beta.
$$

那么：

1. `E[θ̂_raw−τ_* |𝒢]=−rᵀβ`，而 `E[θ̂_db|𝒢]=τ_*`。
2. 精确条件方差为

$$
V=\sum_{i\in C}\alpha_i^2v_i+\sum_{j\in J}h_j^2v_j
=\alpha^\top\Sigma_C\alpha+
r^\top G^{-1}X^\top W\Sigma_JWXG^{-1}r,
\tag{T2}
$$

其中 `Σ_C=diag(v_i)`、`Σ_J=diag(v_j)`。

3. 有效 MGF proxy 为

$$
S^2=\sum_{i\in C}\alpha_i^2s_i^2+\sum_{j\in J}h_j^2s_j^2.
\tag{T3}
$$

对 `η∈(0,1)`，区间

$$
\left[\widehat\theta_{\rm db}
\pm\sqrt{2S^2\log(2/\eta)}\right]
\tag{T4}
$$

具有至少 `1−η` 的条件覆盖概率。

4. 若 `v_i≤v̄`，则

$$
V\le\bar v\{\|\alpha\|_2^2+w_{\max}\lambda^{-1}\|r\|_2^2\}.
\tag{T5}
$$

若 `s_i²≤s̄²`，则同样有

$$
S^2\le\bar s^2\{\|\alpha\|_2^2+w_{\max}\lambda^{-1}\|r\|_2^2\}.
\tag{T6}
$$

**证明。** 因 `G` 可逆，`BX=I`。代入 `Y_J^0=Xβ+ε_J` 得

$$
\widehat\beta=\beta+B\varepsilon_J.
$$

因此

$$
\widehat\theta_{\rm raw}-\tau_*
=-r^\top\beta+\sum_{i\in C}\alpha_i\varepsilon_i,
$$

以及核心恒等式

$$
\widehat\theta_{\rm db}-\tau_*
=\sum_{i\in C}\alpha_i\varepsilon_i
+r^\top B\varepsilon_J
=\sum_{i\in C}\alpha_i\varepsilon_i
+\sum_{j\in J}h_j\varepsilon_j.
\tag{T7}
$$

取条件期望，使用零均值，证明结论 1。条件独立使交叉协方差为零；对 (T7) 求方差即得 (T2)。把两组权重合并并应用 A.1R，得到 proxy (T3) 及区间 (T4)。

证明范数界时，由 `W²≼w_max W` 可得

$$
\begin{aligned}
\|h\|_2^2
&=r^\top G^{-1}X^\top W^2XG^{-1}r\\
&\le w_{\max}r^\top G^{-1}X^\top WXG^{-1}r\\
&=w_{\max}r^\top G^{-1}r
\le w_{\max}\lambda^{-1}\|r\|_2^2.
\end{aligned}
$$

最后分别用 `v_i≤v̄` 与 `s_i²≤s̄²` 控制 (T2)、(T3)。证毕。

**较弱独立性条件。** 无偏性只需要相应条件均值；方差式只需要对应条件协方差结构；指数尾界需要更强的联合 MGF 控制。这三层不能混在一个未区分的“独立校准”表述中。若重叠研究引起相关误差，可直接假设

$$
\mathbb E[e^{t^\top\varepsilon}\mid\mathcal G]
\le e^{t^\top Kt/2}\quad(t\in\mathbb R^{|C|+|J|}),
$$

其中 `K` 为有效半正定 proxy 矩阵。合并权重 `w=(α,h)` 后使用 `S²=wᵀKw`；实际方差为 `wᵀΣw`。这可替代全体条件独立，但 `K` 的有效性仍需依据。

## 5. Corollary 5.1：必须纳入校准集曲率

### 原结论的反例

取一维机制，`C={c}`、`m_c=0`、`α_c=1`，目标 `m_*=1`；校准机制为 `m_{j1}=2`、`m_{j2}=3`，`W=I`。令 `β=(0,0)`，所有误差为零，`ζ_c=ζ_*=ζ_{j1}=0`、`ζ_{j2}=M`，其中 `M≠0`。

原曲率证书 `|ζ_*−Σα_iζ_i|≤H_qω_C(α)` 可取右边为 0。但是校准回归通过 `(2,0)` 与 `(3,M)`，斜率为 `M`，而 `r=(0,1)ᵀ`，故 `θ̂_db=M`，真值 `τ_*=0`。原区间半径为 0，覆盖率为 0。

这不是抽取噪声问题；即使输入完全正确且研究无噪声，原 Corollary 5.1 也会失败。

### 5.1C-R：完整曲率偏差

把 (T1) 改为

$$
\tau_i=x_i^\top\beta+\zeta_i\quad(i\in C\cup J),
\qquad \tau_*=x_*^\top\beta+\zeta_*.
$$

定义完整偏差

$$
b_{\rm curv}
=\sum_{i\in C}\alpha_i\zeta_i
+\sum_{j\in J}h_j\zeta_j-\zeta_*.
\tag{C1}
$$

若有对 `𝒢` 可测、非负的有效界 `B_curv≥|b_curv|`，则

$$
\left[\widehat\theta_{\rm db}
\pm\{\sqrt{2S^2\log(2/\eta)}+B_{\rm curv}\}\right]
\tag{C2}
$$

具有至少 `1−η` 的条件覆盖概率。

**证明。** 校准回归分解为

$$
\widehat\beta=\beta+B\zeta_J+B\varepsilon_J.
$$

代入得到

$$
\widehat\theta_{\rm db}-\tau_*
=b_{\rm curv}+\sum_{i\in C}\alpha_i\varepsilon_i
+\sum_{j\in J}h_j\varepsilon_j.
\tag{C3}
$$

A.1R 以概率至少 `1−η` 控制后两个和的绝对值，三角不等式再加上 `|b_curv|≤B_curv` 即得 (C2)。证毕。

**可以实际声明的几种曲率证书：**

- 若保留原证书 `|Σ_Cα_iζ_i−ζ_*|≤H_qω_C(α)`，并另有 `|ζ_j|≤k_j`，则可取 `B_curv=H_qω_C(α)+Σ_J|h_j|k_j`。
- 若只掌握 `‖ζ_J‖₂≤K_J`，则可取 `B_curv=H_qω_C(α)+‖h‖₂K_J`，再用 (T5) 前的 `‖h‖₂` 界。
- 若效应函数 `f` 在包含所有相关机制及连接线段的凸域上二阶可微，`‖∇²f‖op≤H`，在目标处取 Taylor 展开，则 `ζ_*=0`，`|ζ_i|≤(H/2)‖m_i−m_*‖²`。因此

$$
B_{\rm curv}
=\frac H2\left\{
\sum_{i\in C}\alpha_i\|m_i-m_*\|^2
+\sum_{j\in J}|h_j|\|m_j-m_*\|^2\right\}
\tag{C4}
$$

是有效界。Taylor 余项来自
`ζ_i=∫₀¹(1−t)(m_i−m_*)ᵀ∇²f(m_*+t(m_i−m_*))(m_i−m_*)dt`。

最后一种证书清楚表现出：校准集距离目标太远也会增加曲率风险。若 `H` 本身是估计的高概率上界，其失败事件应进入总错误预算。

## 6. Proposition 5.1：抽取误差的完整传播

### 6.1 原几何不等式成立，但不能代表完整估计误差

若 `‖m̂_i−m_i‖≤u_i`、`‖m̂_*−m_*‖≤u_*`，则

$$
\left|(r-\widehat r)^\top\beta\right|
\le\|\beta_m\|\left(u_*+\sum_{i\in C}\alpha_i u_i\right).
\tag{E1}
$$

证明是 `r−r̂=(x_*−x̂_*)−Σ_Cα_i(x_i−x̂_i)`；截距坐标均为零，对机制坐标使用 Cauchy–Schwarz 和三角不等式即可。

然而实际算法还把校准设计 `X` 换成 `X̂`，所以 `β̂` 本身改变。(E1) 没有控制这件事。

**反例。** 令真实效应 `f(m)=m`，`C` 的机制为 0，目标为 1，两者抽取完全准确。校准集真机制是 0 和 1，效应也是 0 和 1，但抽取机制是 0 和 2。所有研究和效应抽取均无噪声。抽取后的校准斜率为 `1/2`，最终估计为 `1/2`，目标真值为 1。原式 (5) 仅包含 `C` 和目标的机制误差，半径因此为 0；即使 `L̂_β=1` 完全正确，也不能覆盖真值。

另一个缺口是校准集效应误差：若 `X̂=X` 但 `Ŷ_J−Y_J^0` 非零，它通过 `h_j` 进入最终估计。原式 (5) 的 `Σ_Cα_iv_i` 不含这一项。

原 Assumption 3.4 的
`|(Y_i+b̂_i)−τ_i|≤v̂_i+|Y_i−τ_i|`
也没有清楚定义“理想研究记录”与“文本抽取记录”的差。建议使用下述显式扰动模型；否则研究抽样误差、抽取残差和已校正偏差会重复计算或漏算。

### 6.2 直接在线性权重层面传播误差

保留理想记录 `Y_i^0=τ_i+ε_i`，实际输入定义为

$$
\widetilde Y_i=Y_i^0+\delta_i,
\qquad
\widehat x_i=(1,\widehat m_i^\top)^\top.
$$

在抽取校准事件 `E_ext` 上，所有参与本次推断的来源及目标同时满足

$$
|\delta_i|\le v_i^{\rm ext},\qquad
\|\widehat m_i-m_i\|\le u_i,
\qquad \|\widehat m_*-m_*\|\le u_*.
\tag{E2}
$$

这里 `v_i^{ext}` 是抽取残差幅度，**不是**第 2 节真实条件方差 `v_i`。任何已做偏差校正后的剩余误差都包含在 `δ_i` 内。抽取校准事件不需要与研究误差独立。

令实际算法计算

$$
\widehat G=\widehat X^\top W\widehat X,\quad
\widehat B=\widehat G^{-1}\widehat X^\top W,\quad
\widehat r=\widehat x_*-\sum_{i\in C}\alpha_i\widehat x_i,
\quad
\widehat h=\widehat B^\top\widehat r,
$$

并要求实际矩阵 `Ĝ` 可逆，而非仅真实矩阵 `G` 可逆。记

$$
\widetilde\theta
=\sum_{i\in C}\alpha_i\widetilde Y_i
+\widehat r^\top\widehat B\widetilde Y_J
=\sum_{i\in C}\alpha_i\widetilde Y_i
+\sum_{j\in J}\widehat h_j\widetilde Y_j.
\tag{E3}
$$

实际特征、`α`、`W` 和 `ĥ` 必须对条件信息 `𝒢` 可测，并且理想误差 `ε_i` 在该信息下仍满足 (S2)–(S3)。这项要求可能需要独立的抽取/审计数据；它不会仅由确定了 `ĥ` 自动成立。

在一个额外事件 `E_β` 上令 `‖β_m‖≤L̂`。定义

$$
\begin{aligned}
B_{\rm ext}
={}&\widehat L\left(u_*+\sum_{i\in C}\alpha_i u_i
+\sum_{j\in J}|\widehat h_j|u_j\right)\\
&+\sum_{i\in C}\alpha_i v_i^{\rm ext}
+\sum_{j\in J}|\widehat h_j|v_j^{\rm ext}.
\end{aligned}
\tag{E4}
$$

令 `B̂_curv` 为完整曲率偏差

$$
\left|\sum_{i\in C}\alpha_i\zeta_i
+\sum_{j\in J}\widehat h_j\zeta_j-\zeta_*\right|
\tag{E5}
$$

的有效上界，并定义实际权重的噪声 proxy

$$
\widehat S^2
=\sum_{i\in C}\alpha_i^2s_i^2
+\sum_{j\in J}\widehat h_j^2s_j^2.
\tag{E6}
$$

那么在校准事件上，

$$
\left|\widetilde\theta-\tau_*
-\sum_{i\in C}\alpha_i\varepsilon_i
-\sum_{j\in J}\widehat h_j\varepsilon_j\right|
\le B_{\rm ext}+\widehat B_{\rm curv}.
\tag{E7}
$$

**证明。** 由 `B̂X̂=I`，

$$
\sum_{i\in C}\alpha_i\widehat x_i
+\widehat X^\top\widehat h
=\sum_{i\in C}\alpha_i\widehat x_i+\widehat r
=\widehat x_*.
\tag{E8}
$$

将 `τ_i=x_iᵀβ+ζ_i` 与实际输入分解代入 (E3)，并减去 `τ_*`。仿射部分等于

$$
\begin{aligned}
&\left(\sum_C\alpha_i x_i+\sum_J\widehat h_jx_j-x_*\right)^\top\beta\\
&=\left\{\sum_C\alpha_i(x_i-\widehat x_i)
+\sum_J\widehat h_j(x_j-\widehat x_j)
+(\widehat x_*-x_*)\right\}^\top\beta,
\end{aligned}
\tag{E9}
$$

其中第二个等式由 (E8) 得出。差向量的截距为零，故在 `E_ext∩E_β` 上，(E9) 的绝对值不超过 (E4) 第一行。抽取效应误差和为 `Σ_Cα_iδ_i+Σ_Jĥ_jδ_j`，其绝对值不超过 (E4) 第二行。余下确定性项恰为 (E5)，随机研究误差恰为 (E7) 中被减去的两项。三角不等式给出结论。证毕。

**为何这修复了斜率误差。** (E8) 使用实际抽取矩阵的精确再现恒等式，因而同时包含校准矩阵扰动及其逆矩阵对估计的影响，不需要错误地把 `β̂` 当作固定的真实 `β`。如果抽取矩阵病态，`|ĥ_j|` 会放大 (E4) 和 (E6)，相应风险不会被隐藏。

### 6.3 概率结论及失败预算

设所有证书共同成立的事件为 `E_cert`，`P(E_cert^c)≤ρ`。例如可由并集界取
`ρ=ρ_ext+ρ_β+ρ_curv+ρ_proxy`，其中参数范数、曲率或 proxy 若为确定有效界则对应预算为 0。

在统计 MGF 条件有效时，区间

$$
\widetilde I_\eta=
\left[\widetilde\theta\pm
\left\{\sqrt{2\widehat S^2\log(2/\eta)}
+B_{\rm ext}+\widehat B_{\rm curv}\right\}\right]
\tag{E10}
$$

满足

$$
\mathbb P(\tau_*\notin\widetilde I_\eta)\le\eta+\rho.
\tag{E11}
$$

证明：在 `E_cert` 上，区间失效蕴含研究误差和超过其 A.1R 半径，故
`P(miss)≤P(noise tail)+P(E_cert^c)≤η+ρ`。**不能直接在 `E_ext` 上重新条件化并假定独立性仍在**；这里使用事件包含关系避开了这个问题。

如果 proxy 本身是高概率估计上界，要先有一个真实有效 proxy，且在证书事件上估计半径不小于其半径。原始噪声尾事件仍按真实 proxy 控制，再把证书失败概率相加。仅从数据算出一个小的方差估计并不能得到非渐近保证。

## 7. Theorem 5.2：有限族、任意后续选择及报告语义

### 7.1 5.2R：严格的同时有效性

设候选报告集 `𝓡` 为固定有限集，或为 `𝒢` 可测的有限集；后一情况必须在给定 `𝒢` 后保留每个报告的条件尾界。令错误预算 `η_R≥0` 为 `𝒢` 可测，几乎处处满足

$$
\sum_{R\in\mathcal R}\eta_R\le\alpha.
\tag{M1}
$$

对 `η_R=0` 的报告，采用整条实线作为区间，或另行证明零失效概率；不能直接计算 `log(2/0)`。假设每个报告 `R` 的误差分解、区间与第 6 节一致，并且全部必要证书在共同事件 `E_cert` 上同时成立，`P(E_cert^c)≤ρ`。则

$$
\mathbb P\{\forall R\in\mathcal R:\tau_R\in I_R\}
\ge1-\alpha-\rho.
\tag{M2}
$$

因此对任何依据完整数据选择的可测报告 `R̂∈𝓡` 及任何可测标签规则，

$$
\mathbb P\{\widehat\ell={\rm link},\,
\tau_{\widehat R}\notin I_{\widehat R}\}
\le\alpha+\rho.
\tag{M3}
$$

**证明。** 令 `A_R={τ_R∉I_R}`，`T_R` 为该报告研究误差和超过统计半径的事件。在 `E_cert` 上，由 (E7) 有 `A_R⊆T_R`。条件并集界给出

$$
\mathbb P\left(\bigcup_{R\in\mathcal R}T_R\mid\mathcal G\right)
\le\sum_{R\in\mathcal R}\eta_R\le\alpha.
$$

对条件概率取期望，且
`⋃_R A_R⊆(⋃_R T_R)∪E_cert^c`，得 (M2)。在所有区间同时覆盖的事件上，不论如何选择 `R̂`，其区间都覆盖；故 (M3) 是 (M2) 的直接结果。跨报告误差或区间可以相关，无需报告之间独立。证毕。

这里保证的是**被选择报告失效的无条件概率**。它不自动给出
`P(miss | label=link)≤α+ρ`；若 `P(link)>0`，直接能得到的只是条件失效概率不超过 `(α+ρ)/P(link)`，并可截断为 1。

### 7.2 为什么“候选集有限”不够

令有 `M` 个互相独立的标准正态统计量，各自对应同一真值 0 的普通 `1−α` 区间。先查看全部统计量，再选取绝对值最大的一个，把它作为“唯一候选报告”，并为这个单元素集合分配全部预算 `α`。最终候选集确实有限，甚至大小为 1，但覆盖率为

$$
\mathbb P\left(\max_{1\le j\le M}|Z_j|\le z_{1-\alpha/2}\right)
=(1-\alpha)^M,
$$

远低于 `1−α`。修复方法是预先对完整 `M` 个候选分配错误预算，再允许选择；或用与推断数据独立的数据构造候选族。将筛选后结果写入 `𝒢` 不能恢复筛选前的正态条件分布。

同理，预算若通过同一效应噪声自适应分配，也需证明对应条件覆盖，不能只检查最终预算总和。

### 7.3 Reconcile 的正确解释

若两个区间针对**同一个**目标真值 `τ`，那么同时覆盖意味着 `τ∈I_R∩I_S`，故交集不可能为空。因此原文“在同一个同时有效事件上，reconcile 给出不相交的兼容区间”不能被解释成同一真值下的正常发现。

正确版本有两种，论文应明确选择：

1. **共同目标一致性检验。** 在“这些报告确实对应相同目标且全部识别、抽取和统计假设成立”的联合零假设下，定义 `D={∃R,S:I_R∩I_S=∅}`。由 (M2)，

   $$
   \mathbb P(D)\le\alpha+\rho.
   \tag{M4}
   $$

   若观察到冲突，可以拒绝这一联合假设并要求审计；不能仅凭不交区间判断具体是哪篇研究错误、哪个假设失效，或声称已经解决冲突。

2. **明确不同 estimands。** 若报告目标本来是 `τ_R` 和 `τ_S`，在同时覆盖事件上不交区间确实证明 `τ_R≠τ_S`。此时应说明差异属于人群、处理、结局或环境，不能继续把两者叫同一未知标量。

### 7.4 Bridge 只凭区间覆盖不能证明“真的不支持”

算法可确定性地证明：“本次候选集中没有报告通过所规定的检查”。这不等于已经证明目标在真实机制空间中不可支持，更不等于在所有可能研究组合中不可识别。

令 `d=inf_{α∈Δ_C}‖m_*−Σ_Cα_im_i‖`，`d̂` 为抽取版本。在几何校准事件上，对每个 `α`，逆三角不等式给出

$$
\left|\left\|m_*-\sum_C\alpha_im_i\right\|
-\left\|\widehat m_*-\sum_C\alpha_i\widehat m_i\right\|\right|
\le u_*+\sum_C\alpha_iu_i
\le u_*+\max_{i\in C}u_i.
$$

对两个方向分别取下确界可得

$$
|d-\widehat d|\le u_*+\max_{i\in C}u_i.
\tag{M5}
$$

所以 `d̂>δ` 本身不足以证明 `d>δ`。要证明真实不支持，可以使用
`d̂−u_*−max_i u_i>δ`。要给某组实际权重出具支持证书，可以检查
`‖m̂_*−Σα_im̂_i‖+u_*+Σα_iu_i≤δ`。后者未通过，仅代表**尚不能认证支持**。

此外，点参数置信区间与部分识别集不是同一对象。若 bridge 要对“真实部分识别集”的直径作认证，需另行定义该识别集并证明估计集合对它的包含性质。Theorem 5.2 的点覆盖并不自动提供这项集合保证。

## 8. Theorem 5.3：渐近正态与学生化

### 8.1 任意数据选择为何破坏原解释

设两个候选报告分别使用互相独立的 `N` 个标准正态观测，估计均值 0。记

$$
Z_{r,N}=\frac1{\sqrt N}\sum_{k=1}^N\varepsilon_{r,k},
\quad r=1,2.
$$

对每个固定候选，`Z_{r,N}` 对所有 `N` 都精确服从 `N(0,1)`，也满足 Lindeberg 条件。选择 `r̂=argmax_r|Z_{r,N}|` 后，

$$
\mathbb P(|Z_{\widehat r,N}|\le z)
=\{2\Phi(z)-1\}^2,\quad z\ge0.
\tag{N1}
$$

这个分布不随 `N` 变化且不是标准正态。普通双侧 `1−a` 区间的选择后覆盖为 `(1−a)²`。即使重新按选择后真实方差归一化，最大绝对值所诱导的形状也不会变成正态。

问题在于：选择后加权和中的权重依赖同一批误差，各项不再保留原来的条件独立结构。**同时区间能保护选择后的覆盖，但不能自动把所选估计量的分布变回正态。**

### 8.2 5.3R：可证明的条件三角阵列版本

对于每个 `N`，设有条件信息 `𝒢_N` 及有限行 `(ξ_{N,k})_k`，满足：

1. 给定 `𝒢_N` 后，各项相互独立，条件均值为零，有有限二阶矩。
2. `V_N=Σ_k E[ξ_{N,k}²|𝒢_N]>0` 几乎处处。
3. 对每个 `ε>0`，

$$
L_N(\epsilon)=\frac1{V_N}\sum_k
\mathbb E[\xi_{N,k}^2
1_{\{|\xi_{N,k}|>\epsilon\sqrt{V_N}\}}\mid\mathcal G_N]
\xrightarrow{p}0.
\tag{N2}
$$

4. 实际估计误差可以写成

$$
\widetilde\theta_N-\tau_{*,N}
=\sum_k\xi_{N,k}+b_N+\Delta_N,
\qquad
\frac{b_N+\Delta_N}{\sqrt{V_N}}\xrightarrow{p}0.
\tag{N3}
$$

那么

$$
\frac{\widetilde\theta_N-\tau_{*,N}}{\sqrt{V_N}}
\Rightarrow N(0,1).
\tag{N4}
$$

若另有 `V̂_N>0`（至少以趋于 1 的概率成立）且 `V̂_N/V_N→p1`，则

$$
\frac{\widetilde\theta_N-\tau_{*,N}}{\sqrt{\widehat V_N}}
\Rightarrow N(0,1),
\tag{N5}
$$

固定 `a∈(0,1)` 的普通正态区间覆盖率趋于 `1−a`。

对于 atlas，`ξ` 应取理想研究误差乘以实际条件可测权重；`b_N` 包含第 5 节完整曲率偏差，`Δ_N` 包含第 6 节完整抽取误差。使用“独立数据选择报告”是使条件 1 成立的一种充分方法，固定报告也是。若使用同一效应数据选择报告，就必须另外证明选择后的条件 1–3；不能引用固定报告的证明代替。

### 8.3 逐步证明条件 CLT

写 `Z_{N,k}=ξ_{N,k}/√V_N`，`q_{N,k}=E[Z_{N,k}²|𝒢_N]`，则 `Σ_kq_{N,k}=1`。

**第一步：单项方差消失。** 对任意 `ε>0`，

$$
q_{N,k}
\le\epsilon^2+
\mathbb E[Z_{N,k}^2 1_{\{|Z_{N,k}|>\epsilon\}}\mid\mathcal G_N],
$$

因此 `max_kq_{N,k}≤ε²+L_N(ε)`。先令 `N→∞` 再令 `ε↓0`，得到 `max_kq_{N,k}→p0`。

**第二步：条件特征函数的总余项消失。** 固定实数 `t`，令

$$
\phi_{N,k}(t)
=\mathbb E[e^{itZ_{N,k}}\mid\mathcal G_N]
=1-\frac{t^2}2q_{N,k}+d_{N,k}(t).
$$

利用零均值、Taylor 余项以及全局界
`|e^{iu}−1−iu+u²/2|≤u²`，在 `|Z|≤ε` 与其补集上分别估计得

$$
\sum_k|d_{N,k}(t)|
\le\frac{|t|^3\epsilon}{6}
+t^2L_N(\epsilon).
\tag{N6}
$$

先取足够小的 `ε`，再利用 (N2)，得到总余项趋于 0（依概率）。

**第三步：乘积趋向高斯特征函数。** 设
`a_{N,k}=−t²q_{N,k}/2+d_{N,k}(t)`。前两步给出

$$
\sum_ka_{N,k}\xrightarrow{p}-t^2/2,
\quad\max_k|a_{N,k}|\xrightarrow{p}0,
\quad\sum_k|a_{N,k}|=O_p(1).
$$

因而
`Σ_k|a_{N,k}|²≤max_k|a_{N,k}| Σ_k|a_{N,k}|→p0`。在所有 `|a_{N,k}|≤1/2` 的高概率事件上，复数对数展开满足
`|log(1+a)−a|≤2|a|²`。条件独立性于是给出

$$
\mathbb E\left[e^{it\sum_kZ_{N,k}}\mid\mathcal G_N\right]
=\prod_k\phi_{N,k}(t)
\xrightarrow{p}e^{-t^2/2}.
\tag{N7}
$$

**第四步：从条件特征函数到无条件分布。** (N7) 左端的模不超过 1，所以其依概率收敛蕴含到常数的 `L¹` 收敛：将偏差按 `≤δ` 与 `>δ` 分开，有期望偏差至多 `δ+2P(偏差>δ)`。取全期望，得到无条件特征函数趋于 `e^{-t²/2}`。由特征函数连续性定理，`Σ_kξ_{N,k}/√V_N⇒N(0,1)`。

**第五步：余项与学生化。** (N3) 和 Slutsky 定理给出 (N4)。`√(V_N/V̂_N)→p1` 再次使用 Slutsky 得到 (N5)。令 `z=Φ^{-1}(1−a/2)`，因标准正态分布在 `±z` 无原子，

$$
\mathbb P\left(\left|\frac{\widetilde\theta_N-\tau_{*,N}}
{\sqrt{\widehat V_N}}\right|\le z\right)
\longrightarrow\Phi(z)-\Phi(-z)=1-a.
$$

证毕。

这是一份完整书面概率证明；如需从头在 Lean 内核验证，还必须形式化条件独立、条件特征函数、复对数余项、特征函数连续性定理与 Slutsky 等所依赖定理。不能将这些实质内容写成未证明的 `axiom` 后称整个统计结论已验证。

### 8.4 余项可忽略的可检查充分条件

若存在事件 `E_N`，`P(E_N^c)→0`，在该事件上
`|b_N|≤B_N`、`|Δ_N|≤E_N^{rad}`，且

$$
\frac{B_N+E_N^{\rm rad}}{\sqrt{V_N}}\xrightarrow{p}0,
$$

则对任意 `ε>0`，

$$
\mathbb P(|b_N+\Delta_N|>\epsilon\sqrt{V_N})
\le\mathbb P(E_N^c)+
\mathbb P(B_N+E_N^{\rm rad}>\epsilon\sqrt{V_N})\to0.
$$

这给出 (N3)。注意是相对于 **真实标准差**，而不是仅相对于一个可能极保守的 proxy 尺度。

### 8.5 方差一致性需要自己的条件

原稿标题含“variance consistency”，但正文只是**假设** `V̂_N/V_N→p1`，未构造或证明一致估计量。可增加下述充分条件，而不能说原稿已经证明它。

对 atlas 的真实权重 `w_{N,i}`，设

$$
V_N=\sum_iw_{N,i}^2v_{N,i},\qquad
\widehat V_N=\sum_iw_{N,i}^2\widehat v_{N,i}.
$$

若每项估计非负，且

$$
\frac{\sum_iw_{N,i}^2|\widehat v_{N,i}-v_{N,i}|}{V_N}
\xrightarrow{p}0,
\tag{N8}
$$

则由三角不等式
`|V̂_N/V_N−1|≤Σ_iw_i²|v̂_i−v_i|/V_N→p0`。这是充分条件的完整证明。更强但容易陈述的条件是：对所有具有非零权重的正方差项，最大相对估计误差趋于零；真方差为零的项还需单独控制估计贡献。

要进一步证明 (N8)，需说明每个研究提供何种标准误、研究内部样本量怎样增长、研究间是否重叠，以及方差估计的误差控制。仅每项有一个效应数值不能无条件得到这样的结论。若采用 proxy 而非真实方差，通常只能获得保守推断，不能自动得到标准正态学生化。

### 8.6 非可忽略半径：保证为下界，而非精确覆盖

若偏差和抽取误差不满足 (N3)，但以概率至少 `1−ρ_N` 有
`|b_N|≤B_N`、`|Δ_N|≤E_N^{rad}`，且噪声中心部分满足上述 CLT 和方差一致性，则扩大区间

$$
\left[\widetilde\theta_N\pm
\{z_{1-a/2}\sqrt{\widehat V_N}+B_N+E_N^{\rm rad}\}\right]
\tag{N9}
$$

满足

$$
\liminf_N\mathbb P\{\tau_{*,N}\in I_N\}
\ge1-a-\limsup_N\rho_N.
\tag{N10}
$$

因为证书成立且噪声和绝对值不超过正态半径时，三角不等式保证覆盖。若 `ρ_N→0`，得到至少 `1−a` 的渐近覆盖。一般**不等于** `1−a`：例如在零偏差下人为加入远大于标准差的有效上界，覆盖会趋于 1。

如果还要任意选择报告，应对固定有限候选族分别用分配后的显著性水平构造区间，再用第 7 节并集论证。这给选择后的覆盖，仍不证明选择后估计量正态。候选数随 `N` 增长时，逐个 `o(1)` 覆盖误差不够；需要这些误差之和趋于零、足够统一的近似速率，或者回到有限样本同时区间。

## 9. 可供 Lean 工作拆分的精确接口

以下区分建议旨在避免把“形式化了代数”混称为“形式化了全部统计理论”。

1. **有限维确定性代数层**：`BX=I` 推出去偏分解 (T7)；带曲率分解 (C3)；观察设计再现 (E8)；抽取误差分解 (E9)。这些适合先证明，不能单独推出覆盖率。
2. **有限和与范数层**：Cauchy–Schwarz、三角不等式给 (E1)、(E4)、(E7)、(M5)；非负有限和和概率并集界给 (M2)–(M4)。输入事件及其概率界应明确标为假设。
3. **矩阵谱层**：正定可逆、Loewner 次序与谱下界给 (T5)–(T6)。若暂未形式化，应把 `‖h‖²≤w_max λ⁻¹‖r‖²` 作为明示接口并注明矩阵推导只具书面证明。
4. **概率层**：条件 MGF 的乘积、Chernoff 优化、A.1R、真实方差计算及覆盖。不能以“输入 already has tail bound”取代完整 A.1R 后声称浓缩定理已证明；那只能称覆盖传递引理。
5. **渐近层**：三角阵列条件 CLT、余项忽略、方差一致性及 Slutsky。若当前环境没有所需库支持，应诚实列为未形式化，不用 `sorry`、`admit`、用户自定义 `axiom` 或把结论整体当作假设来伪装完成。

建议主论文使用第 2 节统一前提与 (E3)–(E11) 作为实际引擎的核心有限样本定理；把真实特征版 5.1R 作为解释去偏机制的基础命题。这样实际算法、抽取误差和统计保证对应的是同一个估计量。
