# Exact powers of two in cubic lattice spheres

Let $C(h,d)$ count the vectors in $\mathbb Z^h$ whose coordinates have total absolute value $d$, for $h,d\ge1$. This is the cubic lattice coordination array A035607. Since one coordinate has generating function $f(x)=1+2x+2x^2+\cdots=(1+x)/(1-x)$, we have $C(h,d)=[x^d]f(x)^h$. The row array A363418 satisfies $T(n,k)=C(k,nk)$.

Write $v_2(m)$ for the number of factors of 2 in a positive integer. The exact valuation is
```math
v_2(C(h,d))=
\begin{cases}
1+v_2(h),&d\text{ odd},\\
1,&d\text{ even and }h\text{ odd},\\
2v_2(h)+v_2(d),&h,d\text{ both even}.
\end{cases}
\tag{1}
```

## Derivation

Write $s=v_2(h)$, $t=v_2(d)$ and set $H(x)=\sum_{j\ge1,\ j\ {\rm odd}}x^j/j$. All its coefficients have odd denominators. In rational formal power series $\log f=2H$, so
```math
C(h,d)=\sum_{j=1}^d\frac{(2h)^j}{j!}[x^d]H^j .
\tag{2}
```
Only $j$ of the same parity as $d$ contribute.

If $d$ is odd, the term $j=1$ equals $2h/d$ and has valuation $s+1$. For odd $j\ge3$, $v_2(j!)\le j-2$, so each other term has valuation at least $js+2\ge s+2$. This proves the first line of (1).

The count according to the number of nonzero coordinates gives
```math
C(h,d)=\sum_{j=1}^{\min(h,d)}
  2^j\binom hj\binom{d-1}{j-1},\qquad
dC(h,d)=hC(d,h).
\tag{3}
```
The second identity follows by replacing $d\binom{d-1}{j-1}$ by $j\binom dj$ in the sum. This proves the second line of (1) by exchanging dimension and distance.

Suppose now that $s,t\ge1$. By (3) it suffices to treat $s\ge t$. In fact swapping $h,d$ changes the predicted valuation from $2s+t$ to $2t+s$, and the factors in (3) account exactly for the difference.

The quadratic coefficient that controls (2) is
```math
[x^d]H^2=\sum_{1\le j<d,\ j\ {\rm odd}}\frac1{j(d-j)}
\equiv-\sum_{1\le j<d,\ j\ {\rm odd}}\frac1{j^2}
\pmod {2^t}.
```
Inversion permutes the odd residues modulo $2^t$. There are $d/2^t$ complete blocks, an odd number. In each block the sum of inverse squares is congruent to the sum of the odd squares. For $m=2^{t-1}$ the latter equals $m(4m^2-1)/3$ and has valuation $t-1$. Thus $v_2([x^d]H^2)=t-1$.

The $j=2$ term in (2) now has valuation $1+2s+t-1=2s+t$. For even $j\ge4$ use $v_2(j!)\le j-1$. Its term has valuation at least $js+1\ge4s+1>2s+t$, using $s\ge t\ge1$. A unique term has smallest valuation, which proves (1).

## The excluded prime for A363418

For $n,k\ge1$, formula (1) specializes to
```math
v_2(T(n,k)) =
\begin{cases}
1,& k\text{ odd},\\
3v_2(k)+v_2(n),& k\text{ even}.
\end{cases}
```
If $k$ is odd and $n$ is even, use the second line of (1). For $k$ even put $t=v_2(k)$ and $s=v_2(n)$. The successive terms have different valuations, so their difference has the smaller one:
```math
v_2\bigl(T(n,k)-T(n,k/2)\bigr)=
\begin{cases}
1,&t=1,\\
3t-3+s,&t\ge2 .
\end{cases}
```
For example, $T(4,4)=11008$ and $T(4,2)=32$. Their difference is $10976=2^5\cdot343$, attaining $3\cdot2-3+v_2(4)=5$.

## Sources and verification

The OEIS entries give the two arrays, the coefficient formulas, and Bala's conjecture for primes at least five. The exact binary classifications above are derived from those definitions. No claim of first discovery is made.

- [A035607, coordination numbers of the cubic lattice](https://oeis.org/A035607)
- [A363418, Peter Bala's array](https://oeis.org/A363418)
- [Independent exact coefficient verifier](verify.py)
