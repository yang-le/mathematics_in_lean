# 序和可整除性

$\min(a, b)$定义为所有小于等于$a, b$的元素中最大的那个。具体来说，可以如下事实刻画

$$\begin{align}
\min(a, b) \le a \\
\min(a, b) \le b \\
c \le a \land c \le b \implies c \le \min(a, b)
\end{align}$$

也可以写成
$$\begin{equation*}
c \le a \land c \le b \iff c \le \min(a, b)
\end{equation*}$$

实际上可以证明
$$\begin{equation*}
\min(a, b) \le a \land \min(a, b) \le b \iff c \le \min(a, b) \implies c \le a \land c \le b
\end{equation*}$$
从左往右$c \le \min(a, b)$且$\min(a, b) \le a$得出$c \le a$，同理可得$c \le b$；从右往左只需注意到$\min(a, b) \le \min(a, b)$即可。

$\min$满足交换律
$$\begin{equation}
\min(a, b) = \min(b, a)
\end{equation}$$

为此只需证明$\min(a, b) \le \min(b, a)$以及$\min(b, a) \le \min(a, b)$。
根据公理$(1)(2)$，我们有$\min(a, b) \le b \land \min(a, b) \le a$，于是根据公理$(3)$就有$\min(a, b) \le \min(b, a)$。
同理可证另一半。

$\min$满足结合律
$$\begin{equation}
\min(\min(a, b), c) = \min(a, \min(b, c))
\end{equation}$$

我们先来说明$\min(\min(a, b), c) \le \min(a, \min(b, c))$，为此要证明
- $\min(\min(a, b), c) \le a$

    由$\min(\min(a, b), c) \le \min(a, b) \le a$可证

- $\min(\min(a, b), c) \le \min(b, c)$

    由$\min(\min(a, b), c) \le \min(a, b) \le b$以及$\min(\min(a, b), c) \le c$再结合公理$(3)$可证

再使用公理$(3)$完成证明。类似地可以证明$\min(a, \min(b, c)) \le \min(\min(a, b), c)$，于是就得到了两者的相等性。

$\max(a, b)$定义为所有大于等于$a, b$的元素中最小的那个。也有类似的公理

$$\begin{align}
\max(a, b) \ge a \\
\max(a, b) \ge b \\
c \ge a \land c \ge b \implies c \ge \max(a, b)
\end{align}$$

不难证明，$\max$也是交换和结合的
$$\begin{align}
\max(a, b) &= \max(b, a) \\
\max(\max(a, b), c) &= \max(a, \max(b, c))
\end{align}$$

引理
$$\begin{equation*}
\min(a, b) + c \le \min(a + c, b + c)
\end{equation*}$$

仍然是使用公理，我们有$\min(a, b) \le a$，即$\min(a, b) + c \le a + c$；类似地$\min(a, b) + c \le b + c$，这就完成了证明。

实际上可以证明
$$\begin{equation}
\min(a, b) + c = \min(a + c, b + c)
\end{equation}$$

为此我们只需说明$\min(a + c, b + c) \le \min(a, b) + c$，再结合引理即可完成证明。
而根据引理$\min(a + c, b + c) + -c \le \min(a, b)$，这正是我们要证明的。

> 用三角不等式
> $$|a + b| \le |a| + |b|$$
> 证明另一个
> $$|a - b| \ge |a| - |b|$$
> 证明：
> $$|a| - |b| = |a - b + b| - |b| \le |a - b| + |b| - |b| = |a - b|$$
> 直观的解释是三角形的两边之和大于第三边，且它们的差（的绝对值）小于第三边，即
> $$||a| - |b|| \le |a \pm b| \le |a| + |b|$$

## 可整除性和最大公约数

可整除性也是一种偏序关系。所谓偏序关系是一种满足自反、传递和反对称的关系。最大公约数和最小公倍数之于整除就类似于最大和最小之于$\le$。
其公理是完全类似的
$$\begin{align}
\gcd(a, b) \mid a \\
\gcd(a, b) \mid b \\
c \mid a \land c \mid b \implies c \mid \gcd(a, b)
\end{align}$$

可以证明类似的性质，如交换律、结合律。
$$\begin{equation}
\gcd(a, b) = \gcd(b, a)
\end{equation}$$

对最小公倍数的讨论也是类似的。
