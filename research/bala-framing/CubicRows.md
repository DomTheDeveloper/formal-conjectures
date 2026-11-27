# Cubic congruences for the rows of A363418 and A363419

Peter Bala proposed the following congruence for each positive row of both arrays. When a prime $p\ge5$ divides the row number, the proof below gives an additional power for each factor of $p$ in that number. It also proves the proposed extension of A363419 to negative rows.

For integers $a,b,n$ with $n\ne0$, write $f=(1+x)^a(1-x)^b$ and
```math
T_n(k)=\frac{1}{n}[x^k]f(x)^{nk},\qquad k\ge1.
```
Fix an odd prime $p$, an index $N>0$ divisible by $p$, and put $M=N/p, t=v_p(N), s=v_p(n)$. Set $\delta=1$ for $p=3$ and $\delta=0$ otherwise. Then
```math
p^{3t+s-\delta}\ \mid\ T_n(N)-T_n(M).
\tag{1}
```
Both terms are integers. Indeed, differentiating $f^{nk}$ gives $T_n(k)=[x^{k-1}]f^{nk-1}f'$, including for $n<0$.

## The two arrays

For A363419 take $(a,b)=(-1,-2)$, since $(1-x)(1-x^2)=(1-x)^2(1+x)$. This substitution applies verbatim to negative rows.

For A363418 take $(a,b)=(1,-1)$. To match the order of the exponents in its definition, put $C(h,d)=[x^d]((1+x)/(1-x))^h$. Expanding $(1+2x/(1-x))^h$ for positive $h,d$ gives
```math
d C(h,d)=\sum_{j=1}^{\min(h,d)}
j\,2^j\binom hj\binom dj=h C(d,h).
```
Consequently $C(k,nk)=C(nk,k)/n$ for positive $n,k$. In (1) substitute $N=mp^r$. Since $t=r+v_p(m)$, this proves the proposed modulus $p^{3r}$ for every prime $p\ge5$.

## Proof of (1)

Work with formal series over the $p$-adic integers and their fraction field. Define $w_j=a(-1)^{j+1}-b$ and
```math
L(x)=\sum_{j\ge1,\ p\nmid j}\frac{w_j}{j}x^j.
```
The logarithm of $f$ is $\sum_{j\ge1}w_j x^j/j$. Since $w_{pj}=w_j$ for odd $p$, cancellation gives
$L=\log f(x)-p^{-1}\log f(x^p)$.
Let $G(x)=x^{-1}f(x)^n$. With $\operatorname{CT}$ denoting the constant coefficient,
```math
n(T_n(N)-T_n(M))
=\operatorname{CT}\bigl(G(x^p)^M(\exp(nNL)-1)\bigr).
\tag{2}
```
All extractions involve only finitely many terms. The linear contribution vanishes because one factor has only exponents divisible by $p$ and the other has none.

For the quadratic contribution take $T>0$ divisible by $p$, and $e=v_p(T)$. Reduction modulo $p^e$ gives
```math
[x^T]L^2
\equiv-\sum_{1\le j<T,\ p\nmid j}\frac{w_j w_{T-j}}{j^2}\pmod{p^e}.
\tag{3}
```
For a complete interval of length $p^e$ the sum $S$ of inverse squares over unit residues satisfies $3S=0\pmod{p^e}$. Indeed, multiplication by 2 permutes the units and rescales the sum by $1/4$. Thus $S=0\pmod{p^{e-\delta}}$. If $T$ is odd, $w_jw_{T-j}$ is constant. If $T$ is even, it has separate constant values on the even and odd indices. The even part of the unweighted sum is $1/4$ of the same sum up to $T/2$, which is again a multiple of $p^e$. Subtraction gives the odd part. In both cases (3) yields
```math
v_p([x^T]L^2)\ge e-\delta .
\tag{4}
```

For the matching coefficient $g=[x^{-T/p}]G^M$, logarithmic differentiation in the form $x(G^M)'=M G^{M-1}xG'$ shows that $(-T/p)g$ is divisible by $M$ in the local integer ring. Hence $v_p(g)\ge\max(0,t-e)$. Every term of $\operatorname{CT}(G(x^p)^M L^2)$ is therefore divisible by $p^{t-\delta}$. Multiplication by $(nN)^2/(2n)$ gives the exponent $3t+s-\delta$.

For degree $j\ge3$, the other series have integral coefficients. The bound $v_p(j!)\le j-3+\delta$ follows directly from Legendre's formula, treating $j=3,4$ separately for $p\ge5$. Thus $v_p((nN)^j/(n j!))\ge3t+2s-\delta$. Together these estimates prove (1).

## Sharp cases

| Array | $p,n,N$ | $T_n(N)-T_n(N/p)$ | Exact valuation |
|---|---|---:|---:|
| A363418 | $5,1,5$ | 1000 | 3 |
| A363419 | $5,1,5$ | 375 | 3 |
| A363418 | $3,1,3$ | 36 | 2 |
| A363419 | $3,1,3$ | 18 | 2 |
| A363418 | $5,5,10$ | 5644536540000 | 4 |
| A363419 | $5,-5,5$ | 625 | 4 |

The final row has $T_{-5}(5)=626$ and $T_{-5}(1)=1$. Thus the extra factor survives the division by the row number and the exponent is attained.

## Attribution

Peter Bala posed the questions. The public proof candidate in the rbajaj5 repository treats the unnormalized period-two family and arbitrary integral coefficient slopes, directly covering the original positive-row A363418 congruence. Its reduced-logarithm approach is the antecedent of (2). The proof here tracks the row divisor through every term, gives a short inverse-square calculation for (4), and treats both signed normalized arrays. The formal framing connection also appears in L. Felipe Müller's 2021 preprint. The argument above uses only the period-two calculation and establishes the displayed bounds directly. Priority of the strengthened bounds is unestablished.

- [A363418](https://oeis.org/A363418)
- [A363419](https://oeis.org/A363419)
- [Prior coefficient-family argument, sections 4.1–4.5](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/CoefficientFramingCubicTower.md)
- [L. Felipe Müller, Wolstenholme Type Congruences and Framing of Rational 2-Functions](https://arxiv.org/abs/2104.10754)
