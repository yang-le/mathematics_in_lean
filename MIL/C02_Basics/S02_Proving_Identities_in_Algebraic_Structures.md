# 证明代数结构中的等式

## 环

称集合$R$及其上的运算$+, \times$为环，如果：
- $R$与$+$构成阿贝尔群
- $R$与$\times$构成幺半群
- $\times$对$+$有分配律

具体来说，有如下公理
- 加法结合律
$$\begin{equation}
\forall a, b, c \in R, ~ a + b + c = a + (b + c)
\end{equation}$$
- 加法交换律
$$\begin{equation}
\forall a, b \in R, ~ a + b = b + a
\end{equation}$$
- 左零元
$$\begin{equation}
\exist 0 \in R, \forall a \in R, ~ 0 + a = a
\end{equation}$$
- 加法左逆元
$$\begin{equation}
\forall a \in R, \exist -a \in R, ~ -a + a = 0
\end{equation}$$
- 乘法结合律
$$\begin{equation}
\forall a, b, c \in R, ~ a \times b \times c = a \times (b \times c)
\end{equation}$$
- 单位元
$$\begin{equation}
\exist 1 \in R, \forall a \in R, ~ 1 \times a = a \times 1 = a
\end{equation}$$
- 分配律
$$\begin{align}
\forall a, b, c \in R, ~ a \times (b + c) = a \times b + a \times c \\
\forall a, b, c \in R, ~ (a + b) \times c = a \times c + b \times c
\end{align}$$

使用公理$(2), (3)$，容易证明
$$\begin{equation}
\forall a \in R, ~ a + 0 = a
\end{equation}$$

使用公理$(2), (4)$，容易证明
$$\begin{equation}
\forall a \in R, ~ a + -a = 0
\end{equation}$$

下面的定理常常是有用的
$$\begin{equation}
\forall a, b \in R, ~ -a + (a + b) = b
\end{equation}$$
使用公理$(1),(4),(3)$即可证明。

类似地
$$\begin{equation}
\forall a, b \in R, ~ a + b + -b = a
\end{equation}$$
使用公理$(1)$以及定理$(10), (9)$即可。

以上两个定理可以用来证明下面的
$$\begin{equation}
\forall a, b, c \in R, ~ a + b = a + c \implies b = c
\end{equation}$$

证明：
使用定理$(11)$，右边就是$-a + (a + b) = c$；代入前提条件得$-a + (a + c) = c$；再次使用定理$(11)$即可。

以及

$$\begin{equation}
\forall a, b, c \in R, ~ a + b = c + b \implies a = c
\end{equation}$$

证明：
使用定理$(12)$，右边就是$a + b + -b = c$；代入前提条件得$c + b + -b = c$；再次使用定理$(12)$即可。

进一步地
$$\begin{equation}
\forall a \in R, ~ a \times 0 = 0
\end{equation}$$

证明：
使用定理$(13)$，只需证明$a \times 0 + a \times 0 = a \times 0 + 0$即可。
而这又可以使用公理$(7)$和定理$(9)$证明。

类似地
$$\begin{equation}
\forall a \in R, ~ 0 \times a = 0
\end{equation}$$

证明：
使用定理$(14)$，只需证明$0 \times a + 0 \times a = 0 + 0 \times a$即可。
而这又可以使用公理$(8), (3)$证明。

以下是一些常用的结论
$$\begin{equation}
\forall a, b \in R, ~ a + b = 0 \implies -a = b
\end{equation}$$

证明：
使用定理$(13)$，只需要证明$a + -a = a + b$即可。使用定理$(10)$并结合前提条件得证。

类似地
$$\begin{equation}
\forall a, b \in R, ~ a + b = 0 \implies a = -b
\end{equation}$$

证明：
使用定理$(14)$，只需要证明$a + b = -b + b$即可。使用公理$(4)$并结合前提条件得证。

$$\begin{equation}
-0 = 0
\end{equation}$$

证明：
使用定理$(17)$，只需要证明$0 + 0 = 0$，这就是公理$(3)$。

$$\begin{equation}
\forall a \in R, ~ --a = a
\end{equation}$$

证明：
使用定理$(17)$，只需要证明$-a + a = 0$，这就是公理$(4)$。

定义：
我们将$a + -b$记作$a - b$。即
$$\begin{equation}
\forall a, b \in R, ~ a - b = a + -b
\end{equation}$$

定理
$$\begin{equation}
\forall a \in R, ~ a - a = 0
\end{equation}$$

证明：
根据定义$(21)$，我们需要证明$a + -a = 0$，这就是定理$(10)$。

最后我们要说明
$$\begin{equation}
\forall a \in R, ~ 2 \times a = a + a
\end{equation}$$

证明：
$$\begin{align*}
2 \times a &= (1 + 1) \times a \\
&= 1 \times a + 1 \times a \\
&= a + a
\end{align*}$$
即使用公理$(8), (6)$。

## 群

上面的一些定理并不需要环结构甚至加法交换律，只需要群结构就够了。
称集合$G$是一个群，如果其上有运算$\cdot$，满足以下三条公理

- 结合律
$$\begin{equation}
\forall a, b, c \in G, ~ a \cdot b \cdot c = a \cdot (b \cdot c)
\end{equation}$$
- 左幺元
$$\begin{equation}
\exist 1 \in G, \forall a \in G, ~ 1 \cdot a = a
\end{equation}$$
- 左逆元
$$\begin{equation}
\forall a \in G, ~ \exist a^{-1} \in G, ~ a^{-1} \cdot a = 1
\end{equation}$$

> 这里的运算默认是左结合的，即$a \cdot b \cdot c = (a \cdot b) \cdot c$，这可以使我们省去很多不必要的括号。

我们有如下定理：

- 左逆元也是右逆元
$$\begin{equation}
a \cdot a^{-1} = 1, ~ \forall a \in G
\end{equation}$$

证明：

一方面
$$\begin{align*}
(a \cdot a^{-1})^{-1} \cdot (a \cdot a^{-1}) \cdot a \cdot a^{-1} &= 1 \cdot a \cdot a^{-1} \\
&= a \cdot a^{-1}
\end{align*}$$
其中第一个等号使用了公理$(26)$，第二个等号使用了公理$(25)$.

另一方面
$$\begin{align*}
(a \cdot a^{-1})^{-1} \cdot (a \cdot a^{-1}) \cdot a \cdot a^{-1} &= (a \cdot a^{-1})^{-1} \cdot a \cdot a^{-1} \cdot a \cdot a^{-1} \\
&= (a \cdot a^{-1})^{-1} \cdot a \cdot (a^{-1} \cdot a) \cdot a^{-1} \\
&= (a \cdot a^{-1})^{-1} \cdot a \cdot 1 \cdot a^{-1} \\
&= (a \cdot a^{-1})^{-1} \cdot a \cdot (1 \cdot a^{-1}) \\
&= (a \cdot a^{-1})^{-1} \cdot a \cdot a^{-1} \\
&= (a \cdot a^{-1})^{-1} \cdot (a \cdot a^{-1}) \\
&= 1
\end{align*}$$
即依次使用公理$(24), (24), (26), (24), (25), (24), (26)$.

- 左幺元也是右幺元
$$\begin{equation}
a \cdot 1 = a, ~ \forall a \in G
\end{equation}$$

证明：

$$\begin{align*}
a \cdot 1 &= a \cdot (a^{-1} \cdot a) \\
&= a \cdot a^{-1} \cdot a \\
&= 1 \cdot a \\
&= a
\end{align*}$$
即依次使用公理$(26), (24)$，定理$(27)$，公理$(25)$.

- 运算的逆
$$\begin{equation}
(a \cdot b)^{-1} = b^{-1}\cdot a^{-1}, ~ \forall a, b \in G
\end{equation}$$

证明：

一方面
$$\begin{align*}
(a \cdot b)^{-1} \cdot a \cdot b \cdot b^{-1} \cdot a^{-1} &= (a \cdot b)^{-1} \cdot a \cdot (b \cdot b^{-1}) \cdot a^{-1} \\
&= (a \cdot b)^{-1} \cdot a \cdot 1 \cdot a^{-1} \\
&= (a \cdot b)^{-1} \cdot a \cdot a^{-1} \\
&= (a \cdot b)^{-1} \cdot (a \cdot a^{-1}) \\
&= (a \cdot b)^{-1} \cdot 1 \\
&= (a \cdot b)^{-1}
\end{align*}$$
即依次使用公理$(24)$，定理$(27), (28)$，公理$(24)$，定理$(27), (28)$.

另一方面
$$\begin{align*}
(a \cdot b)^{-1} \cdot a \cdot b \cdot b^{-1} \cdot a^{-1} &= (a \cdot b)^{-1} \cdot (a \cdot b) \cdot b^{-1} \cdot a^{-1} \\
&= 1 \cdot b^{-1} \cdot a^{-1}  \\
&= b^{-1} \cdot a^{-1}
\end{align*}$$
即依次使用公理$(24), (26), (25)$.
