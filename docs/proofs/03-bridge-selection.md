# Theorem 5.5：桥接实验选择的完整证明与形式化范围

## 1. 原稿结论及必须明确的条件

原稿第 11 页、附录 B.8 研究基于估计边际收益的贪心桥接选择。证明思路正确，但应在定理中明确以下条件：

- 候选集 $V$ 有限；预算为整数 $B$，且 $1\le B\le |V|$。
- $F:2^V\to\mathbb R$ 满足 $F(\varnothing)=0$，且关于集合包含单调。
- $0<\gamma\le1$，$\varepsilon\ge0$。
- 对所需的 $S,T\subseteq V$，弱次模比条件采用明确约定
  $$\gamma\bigl(F(S\cup T)-F(S)\bigr)\le\sum_{v\in T\setminus S}\bigl(F(S\cup\{v\})-F(S)\bigr).$$
  本证明只需 $|S|<B$、$|T|\le B$ 的情形。
- $\Delta(v\mid S)=F(S\cup\{v\})-F(S)$，且 $|\widehat\Delta(v\mid S)-\Delta(v\mid S)|\le\varepsilon$ 对所需的所有状态和可选元素同时成立。
- 从 $S_0=\varnothing$ 开始，$u_t\in\arg\max_{v\in V\setminus S_t}\widehat\Delta(v\mid S_t)$，$S_{t+1}=S_t\cup\{u_t\}$，$0\le t<B$。

由于候选集有限且 $|S_t|=t<B\le|V|$，上述最大值确实取得。最优集合 $S^*\in\arg\max_{|S|\le B}F(S)$ 也存在；记 $\mathrm{OPT}=F(S^*)\ge0$。

**适用边界。** $F(S)=\operatorname{diam}(\Theta_A)-\mathbb E[\operatorname{diam}(\Theta_{A\cup S})]$ 这一写法本身不能推出单调性或弱次模性。更新后的区间可能因重新校准而变宽；两项实验也可能具有强互补性。本文的贪心近似保证是以上假设下的条件性结论，不能同时作为这些假设已经满足的证明。如值估计界仅以概率 $1-\delta$ 成立，则以下结论在该同时事件上成立，因而其保证概率至少为 $1-\delta$。

## 2. 单步估计误差：严格的 $2\varepsilon$ 界

固定当前集合 $S_t$，令 $v$ 是任一尚未选入的候选。贪心性质及两次误差界给出

$$
\begin{aligned}
\Delta(u_t\mid S_t)
&\ge\widehat\Delta(u_t\mid S_t)-\varepsilon\\
&\ge\widehat\Delta(v\mid S_t)-\varepsilon\\
&\ge\Delta(v\mid S_t)-2\varepsilon.
\end{aligned}
$$

尤其取 $v$ 为当前状态下的真实最优候选，即

$$\Delta(u_t\mid S_t)\ge\max_{v\in V\setminus S_t}\Delta(v\mid S_t)-2\varepsilon.$$

这里的比较对象在**同一当前集合** $S_t$ 上。它不表示含噪贪心序列与一个从头独立运行的真实贪心序列每步累计只差 $2\varepsilon$。

## 3. 从弱次模性推出单步进展

记 $D_t=\mathrm{OPT}-F(S_t)$。由于 $|S_t|\le B$，最优性的定义给出 $D_t\ge0$。单调性给出

$$F(S_t\cup S^*)-F(S_t)\ge F(S^*)-F(S_t)=D_t.$$

弱次模性因此给出

$$\sum_{v\in S^*\setminus S_t}\Delta(v\mid S_t)\ge\gamma D_t.$$

若 $D_t>0$，则 $S^*\setminus S_t$ 非空；其大小至多为 $B$，故至少一个 $v\in S^*\setminus S_t$ 满足

$$\Delta(v\mid S_t)\ge\frac{\gamma}{B}D_t.$$

若 $D_t=0$，单调性说明每个可选候选的真实增益非负，同样满足最大增益至少为 $\gamma D_t/B=0$。故两种情形均有

$$F(S_{t+1})-F(S_t)\ge\frac\gamma B\bigl(\mathrm{OPT}-F(S_t)\bigr)-2\varepsilon.$$

等价地，令 $q=1-\gamma/B\in[0,1)$，则

$$D_{t+1}\le qD_t+2\varepsilon.$$

## 4. 递推展开与有限预算精确界

对 $t=0,\ldots,B$ 归纳证明

$$D_t\le q^t\mathrm{OPT}+2\varepsilon\sum_{j=0}^{t-1}q^j.$$

$t=0$ 时 $D_0=\mathrm{OPT}$。若式子对 $t$ 成立，由 $q\ge0$ 可乘以 $q$ 并保留不等号，再代入递推得到

$$
D_{t+1}\le q^{t+1}\mathrm{OPT}+2\varepsilon\left(1+\sum_{j=0}^{t-1}q^{j+1}\right)
=q^{t+1}\mathrm{OPT}+2\varepsilon\sum_{j=0}^{t}q^j.
$$

由于 $1-q=\gamma/B>0$，几何级数公式给出

$$\sum_{j=0}^{B-1}q^j=\frac{1-q^B}{1-q}=\frac B\gamma(1-q^B).$$

因此有更精确的有限预算保证

$$
\boxed{F(S_B)\ge(1-q^B)\mathrm{OPT}-\frac{2B\varepsilon}{\gamma}(1-q^B).}
$$

该式即使右侧为负也仍然成立；单调性另外给出 $F(S_B)\ge0$，所以可将二者的最大值作为报告的下界。

## 5. 原稿指数形式的结论

对任意实数 $x$，$1+x\le e^x$。取 $x=-\gamma/B$ 得

$$0\le q\le e^{-\gamma/B},\qquad q^B\le e^{-\gamma}.$$

同时 $0\le q^B\le1$，故

$$\sum_{j=0}^{B-1}q^j\le\frac B\gamma.$$

在第 4 节的误差上界中分别使用以上两个界，并利用 $\mathrm{OPT}\ge0$、$\varepsilon\ge0$，得到

$$D_B\le e^{-\gamma}\mathrm{OPT}+\frac{2B\varepsilon}{\gamma}.$$

整理即为

$$\boxed{F(S_B)\ge(1-e^{-\gamma})\max_{|S|\le B}F(S)-\frac{2B\varepsilon}{\gamma}.}$$

若 $\varepsilon=0$，该结论退化为 $\gamma$ 弱次模函数在基数预算下的贪心近似保证。$B=0$ 应单独处理，此时选择空集、价值为零，不能代入包含 $1/B$ 的证明；$\gamma=0$ 也不属于该定理。

## 6. Lean 状态

[Bridge.lean](../../formal/Atlas/Bridge.lean) 验证单步 2ε 损失、弱次模进展、递推与指数界，并以 `weakSubmodular_greedy_bound` 连接集合序列的条件性保证。

形式化采用更简单的几何和上界 ∑qʲ≤B，得到加强的误差项 2Bε，见[总览](README.md)。候选最优集存在、估计 argmax 的具体算法构造和高概率误差事件到各步条件的装配仍在书面层陈述；不声称已对实际引擎的直径目标证明弱次模性。
