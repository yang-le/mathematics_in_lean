# 证明关于代数结构的命题

## 偏序公理

自反性$(1)$、传递性$(2)$和反对称性$(3)$

$$\begin{align}
x \le x \\
x \le y \land y \le z \implies x \le z \\
x \le y \land y \le x \implies x = y
\end{align}$$

对于任何偏序$\le$，都有一个对应的严格偏序$<$，定义为
$$\begin{equation}
x < y \iff x \le y \land x \ne y
\end{equation}$$

严格偏序是反自反$(5)$和传递$(6)$的。
$$\begin{align}
\neg(x < x) \\
x < y \land y < z \implies x < z
\end{align}$$

## 格

格是在偏序集上添加运算$\sqcap$和$\sqcup$的结构，它们类似于$\min$和$\max$，分别称为最大下界和最小上界；或称下确界$\inf$和上确界$\sup$，也被称为交(meet)和并(join)。我们有

$$\begin{align}
x \sqcap y \le x \\
x \sqcap y \le y \\
z \le x \land z \le y \implies z \le x \sqcap y
\end{align}$$

以及

$$\begin{align}
x \sqcup y \ge x \\
x \sqcup y \ge y \\
z \ge x \land z \ge y \implies z \ge x \sqcup y
\end{align}$$

一些格的例子：
- 全序集上的$\min$和$\max$，例如带有$\le$的整数或实数。
- 某个域的子集的$\cap$和$\cup$，其中的序关系是$\subseteq$。
- 布尔值的$\land$和$\lor$，其中的序关系是$x \le y \iff \neg x \lor y$
- （正）自然数上的$\gcd$和$\operatorname{lcm}$，其中的序关系是$\mid$
- 向量空间的线性子空间的集合，其中最大下界由交集给出，最小上界由两个空间的和给出，序是包含关系
- 一个集合上的拓扑的集合，其中两个拓扑的最大下界由它们的并集生成的拓扑给出，最小上界是它们的交集，序是逆包含关系

容易验证下确界和上确界满足交换律和结合律。

> 还容易验证它们满足幂等律
> $$a \sqcup a = a$$
> 以及
> $$a \sqcap  a = a$$
