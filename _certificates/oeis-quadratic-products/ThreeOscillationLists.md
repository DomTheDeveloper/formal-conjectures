# Oscillating primes in three quadratic-product sequences

Write $A_d(n)+B_d(n)\sqrt{-d}=\prod_{k=1}^n(1+k\sqrt{-d})$. For a prime $p$, say that $B_d$ oscillates at $p$ when every tail contains a term coprime to $p$ and, for every $e\ge1$, a nonzero term divisible by $p^e$. This specifies the word “oscillatory,” which the OEIS entries leave informal.

| Sequence | Exact list of oscillating primes |
| --- | --- |
| [A363412](https://oeis.org/A363412), $d=3$ | $p=3$ or $p\equiv5\pmod6$ |
| [A363414](https://oeis.org/A363414), $d=4$ | $p=2$ or $p\equiv3\pmod4$ |
| [A363416](https://oeis.org/A363416), $d=5$ | $p=5$ or $p\equiv11,13,17,19\pmod{20}$ |

**Proof.** The [Lean-verified criterion](https://github.com/DomTheDeveloper/formal-conjectures/blob/1d1909cf4b4a24e6ae6f33284a1c46c038d8effd/_certificates/oeis-quadratic-products/Oscillation.lean) is that $1+dr^2$ has no root in $\mathbb F_p$. At a prime dividing $d$ this polynomial is constantly one, so oscillation holds. At $p=2$ with $d$ odd, $r=1$ gives a root. For odd $p\nmid d$, a root exists exactly when $-d$ is a square, by multiplying by $d$ and setting $u=dr$. We apply quadratic reciprocity.

* For $d=3$, the Legendre symbols satisfy $(-3/p)=(p/3)$ because the signs from $(-1/p)$ and the reciprocity law for $(3/p)$ cancel. For $p\ne2,3$ this is $-1$ exactly when $p\equiv5\pmod6$.
* For $d=4$, $(-4/p)=(-1/p)$, which is $-1$ exactly when $p\equiv3\pmod4$.
* For $d=5$, $(-5/p)=(-1)^{(p-1)/2}(p/5)$. The nonzero squares modulo five are 1 and 4. Evaluating the sign on the eight reduced residue classes modulo twenty gives a negative sign precisely at 11, 13, 17 and 19.

This proves all three lists for every prime under the stated interpretation.

**Independent check.** Compare each list with exhaustive enumeration of the roots modulo every prime through 2000.

```python
from math import isqrt
primes = [p for p in range(2,2001) if all(p % k for k in range(2,isqrt(p)+1))]
for p in primes:
    for d,prediction in ((3,p==3 or p%6==5),
                         (4,p==2 or p%4==3),
                         (5,p==5 or p%20 in (11,13,17,19))):
        assert prediction == all((1+d*r*r)%p for r in range(p))
print("Verified three classifications for",len(primes),"primes each.")
```
