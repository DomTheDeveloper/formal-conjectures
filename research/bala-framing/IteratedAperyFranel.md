# Iterated Apéry and Franel congruences

Peter Bala's two Apéry questions ask for every iterate of an exponential coefficient transform. The Franel question includes the prime 2. The following argument gives all three statements and extends the Franel statement to every iterate.

| OEIS entry | Initial sequence $a_k$ | Transform iterates | Divisibility of $a^{(i)}_{mp^r}-a^{(i)}_{mp^{r-1}}$ |
|---|---|---|---|
| A362724 | $\sum_j\binom kj^2\binom{k+j}j$ | Every $i\ge1$ | $p^{2r}$ for all odd primes |
| A362725 | $\sum_j\binom kj^2\binom{k+j}j^2$ | Every $i\ge1$ | $p^{2r}$ for all odd primes |
| A362731 | $\sum_j\binom kj^3$ | Every $i\ge1$ | $p^{2r}$ for every prime, including 2 |

Here $m,r\ge1$, all binomial sums run from $j=0$ to $k$, and $a^{(0)}=a$. For $i\ge0$, set
```math
E_a(x)=\exp\!\left(\sum_{k\ge1}\frac{a_k}{k}x^k\right),\qquad
T(a)_N=[x^N]E_a(x)^N,\qquad a^{(i+1)}=T(a^{(i)}).
```

## The coefficient estimate that survives each iteration

Suppose $E_a\in1+x\mathbb Z[[x]]$. Fix a prime $p$ for which
$a_k-a_{k/p}$ is divisible by $p^{2v_p(k)}$ whenever $p\mid k$. Assume either that $p$ is odd or that $p=2$ and every $a_k$ for $k>0$ is even. Then $T(a)$ satisfies the same quadratic congruence at $p$.

To prove this, let $N$ be a multiple of $p$, $M=N/p$ and $t=v_p(N)$. Define
```math
D(x)=\log E_a(x)-p^{-1}\log E_a(x^p).
```
For $p\nmid j$, its $j$th coefficient is $a_j/j$. For $p\mid j$, it is $(a_j-a_{j/p})/j$ and has valuation at least $v_p(j)$. Thus $D$ has $p$-integral coefficients. In the binary case every coefficient of $D$ is even, using the even-input hypothesis at the odd indices.

Put $G=x^{-1}E_a$. Comparing the two constant terms gives
```math
T(a)_N-T(a)_M=\operatorname{CT}\,G(x^p)^M\bigl(\exp(ND)-1\bigr).
```
Only indices $j$ divisible by $p$ can occur in the linear term. If $e=v_p(j)$, the matching coefficient $g=[x^{-j/p}]G^M$ satisfies
$v_p(g)\ge\max(0,t-e)$, because $x(G^M)'=M G^{M-1}xG'$ and $G$ has integral Laurent coefficients. Thus $N[x^j]D\cdot g$ has valuation at least $t+e+\max(0,t-e)\ge2t$.

For degree $h\ge2$ and odd $p$, the bound $v_p(h!)\le h-2$ gives $v_p(N^h/h!)\ge2t$. For $p=2$, the factor $D^h$ contributes $2^h$, while $v_2(h!)\le h-1$. Again every contribution is divisible by $p^{2t}$. All coefficient extractions are finite. This proves the estimate.

## Why the hypotheses persist

Let $y=xE_a(y)$. The solution has integer coefficients by coefficient recursion. Lagrange inversion gives
```math
[x^k]\log E_a(y)
=\frac1k[z^{k-1}] E_a(z)^{k-1}E_a'(z)
=\frac1k[z^k]E_a(z)^k .
```
Hence $E_{T(a)}(x)=E_a(y)\in1+x\mathbb Z[[x]]$. Also, differentiating $E_a(x)^N$ yields
```math
T(a)_N=[x^N]\,E_a(x)^N\sum_{j\ge1}a_j x^j .
```
Therefore even positive-index coefficients of the input sequence give even positive-index coefficients of the transformed sequence. The two properties required in the binary proof persist for any number of iterations.

## Applying the estimate

Straub's Theorem 3.2(a) supplies the initial quadratic congruences for all three seeds, including $p=2$. In his notation the block sizes are $(2,1)$, $(2,2)$ and $(1,1,1)$, respectively, on the diagonal with sign $+1$. The same congruences imply the integrality of the initial $E_a$. Indeed, put
```math
c_\ell=\frac1\ell\sum_{d\mid\ell}\mu(\ell/d)a_d .
```
For $p^e\parallel\ell$ the numerator is a sum, with integer weights, of differences $a_{p^e d}-a_{p^{e-1}d}$ with $p\nmid d$. Each is divisible by $p^e$. Thus $c_\ell\in\mathbb Z$, and the Euler product $\prod_{\ell\ge1}(1-x^\ell)^{-c_\ell}=E_a(x)$ has integral coefficients.

Finally, for $k>0$ the Franel sum reduces modulo 2 to $\sum_j\binom kj=2^k=0\bmod 2$, since cubing preserves the parity of an integer. All hypotheses now hold, and induction on $i$ proves the three assertions.

For a small boundary check, the first transformed Franel values at indices $4$ and $2$ are $1954$ and $18$. Their difference is $1936=2^4\cdot121$, attaining the stated exponent at $p=2,r=2$.

## Sources and prior work

The framing theorem of Schwarz, Vologodsky and Walcher is a general antecedent for preservation of quadratic congruences. The proof here gives the coefficient argument in the conventions of these entries and isolates the evenness condition at 2. The named applications use Straub's published input theorem. No priority claim is made.

- [Peter Bala's A362724](https://oeis.org/A362724)
- [Peter Bala's A362725](https://oeis.org/A362725)
- [Peter Bala's A362731](https://oeis.org/A362731)
- [Armin Straub, Multivariate Apéry numbers and supercongruences of rational functions, Theorem 3.2 and Examples 3.4 and 3.6](https://doi.org/10.2140/ant.2014.8.1985)
- [Albert Schwarz, Vadim Vologodsky and Johannes Walcher, Integrality of Framing and Geometric Origin of 2-functions, Theorem 8](https://arxiv.org/abs/1702.07135)
