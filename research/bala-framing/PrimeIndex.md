# Prime indices of A362727 and A362729

For either of these two sequences, write $u_N$ for its term at index $N$. Then $u_p\equiv u_1=2\pmod {p^3}$ for every prime $p\ge5$. This proves the prime-index case of Bala's conjectures, which ask about all $mp^r$ for $p\ge7$. The general parameters $m,r$ remain unresolved here.

## Removing the even powers

For any integer sequence $a_k$ let $E(x)=\exp(\sum_{k\ge1}a_kx^k/k)$ and set $u_N=[x^N](E(x)/E(-x))^N$. Its exponent is $2N\sum_{j\ {\rm odd}} a_jx^j/j$. At an odd prime index $N=p$, its linear term contributes $2a_p$. Every other term contributing to degree $p$ has an odd number $h\ge3$ of factors. Each factor uses an index strictly less than $p$, so the only possible $p$ in the denominator comes from $h!$. For $3\le h<p$ the numerator supplies $p^h$; for $h=p$ it still supplies $p^{p-1}$ after division by $p!$. It follows that
```math
u_p\equiv 2a_p\pmod{p^3}\qquad(p\ge5).
```
This congruence holds in the local ring of rationals with denominators prime to $p$. For the two arrays the coefficients are integers.

## The two binomial seeds

In A362727 and A362729 the respective inputs at $p$ are
```math
a_p=\sum_{k=0}^{p-1}\binom pk\binom{p-1}k\binom{p+k-1}k,\qquad
b_p=\sum_{k=0}^{p-1}\binom pk\binom{p-1}k\binom{p+k}k .
```
Both have constant summand 1. Write $H_j=\sum_{i=1}^j 1/i$ and $S_2=\sum_{k=1}^{p-1}1/k^2$. Multiplication by 2 permutes the nonzero residues modulo $p$, which gives $S_2=0\bmod p$ for $p\ge5$. Pairing $k$ and $p-k$ then gives $2H_{p-1}\equiv-pS_2\equiv0\bmod p^2$.

For $1\le k<p$ the first seed has two summand factors of $p/k$. After extracting them, the three remaining binomial coefficients reduce modulo $p$ to $(-1)^{k-1}$, $(-1)^k$ and $1$. Thus $a_p\equiv1-p^2 S_2\equiv1\bmod p^3$.

For the second seed the $k$th summand equals
```math
-\frac pk\prod_{i<k,\ i\ge1}(1-p/i)\prod_{i=1}^k(1-p^2/i^2)
\equiv -\frac pk(1-pH_{k-1})\pmod{p^3}.
```
Since $2\sum_{k=1}^{p-1}H_{k-1}/k=H_{p-1}^2-S_2\equiv0\bmod p$, summing gives $b_p\equiv1\bmod p^3$. Both assertions follow from the odd-power calculation. At $p=5$ the two differences are $12502-2=12500$ and $18502-2=18500$. At $p=3$ the second sequence gives $146-2=144$, of exact 3-adic valuation two.

- [A362727](https://oeis.org/A362727)
- [A362729](https://oeis.org/A362729)
- [A208675, the first binomial seed](https://oeis.org/A208675)
- [A108628, evaluated at index $p-1$ for the second seed](https://oeis.org/A108628)
