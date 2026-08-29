# 计算

``` lean
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b, mul_comm a c, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm, mul_comm a c, ← mul_assoc]
```

在第一个例子中，交换$c, b$，然后交换右边的$a, c$，最后使用结合律。

在第二个例子中，先对左边使用交换律，然后交换右边的$a, c$，最后反向使用结合律。

``` lean
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, ← mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm, mul_comm a, ← mul_assoc]
```

与上面很类似。

``` lean
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a, h, ← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp, hyp', mul_comm, sub_self]
```

第一个例子，对$a, b, c$使用结合律，然后把$b, c$替换为$e, f$，再反向使用结合律。

第二个例子，对$c, d$做替换，然后交换$b, a$。

``` lean
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw[add_mul, mul_add, mul_add, ← add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
      rw [add_mul]
    _ = a * c + a * d + b * c + b * d := by
      rw [mul_add, mul_add, ← add_assoc]
```

使用`calc`可以写出更结构化的证明。

``` lean
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw[mul_sub, add_mul, add_mul, ← sub_sub, mul_comm a b, ← add_sub, sub_self, add_zero, pow_two, pow_two]
```

$$\begin{align*}
(a + b) \cdot (a - b) &= (a + b) \cdot a - (a + b) \cdot b \\
&= a \cdot a + b \cdot a - (a \cdot b + b \cdot b) \\
&= a \cdot a + b \cdot a - a \cdot b - b \cdot b \\
&= a \cdot a + b \cdot a - b \cdot a - b \cdot b \\
&= a \cdot a + (b \cdot a - b \cdot a) - b \cdot b \\
&= a \cdot a + 0 - b \cdot b \\
&= a \cdot a - b \cdot b \\
&= a^2 - b^2
\end{align*}$$
