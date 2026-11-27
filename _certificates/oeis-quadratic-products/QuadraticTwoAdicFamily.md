# An exact valuation law for every integer $d$ congruent to 3 modulo 8

Let $w^2=-d$ in the free quadratic ring $R=\mathbb Z[w]/(w^2+d)$, and write
$A_n+B_nw=\prod_{k=1}^n(1+kw)$.
For every integer $d\equiv3\pmod8$, $B_n\ne0$ at every positive index. The exponent of two dividing $B_n$ is independent of $d$.

| Index | Conditions | $v_2(B_n)$ |
|---|---|---|
| $8s+1,8s+2$ | $s\ge0$ | $4s$ |
| $8s+3,8s+4,8s+5,8s+6$ | $s\ge0$ | $4s+2$ |
| $8s-1,8s$ | $s\ge1$ | $4s+2+v_2(s)$ |

Consequently $v_2(B_n)=n/2+O(\log(2n))$ with the same implied constant for every such $d$. The case $d=3$ is Peter Bala's 2-adic conjecture for [OEIS A363412](https://oeis.org/A363412).

## Finite polynomial identities

Put $C_h(X)=\prod_{j=1}^h(1+(hX+j)w)$. All congruences are coefficientwise in $R[X]$. For every $d\equiv3\pmod8$,

* $C_4(X)\equiv4w\pmod8$.
* Modulo 256, every nonconstant coefficient of $C_8(X)$ vanishes. The constant has coordinate pair $(48,64)$ or $(240,192)$.

To prove these identities it suffices to check the 32 residues $d=3,11,\ldots,251$, since the coefficient pairs are integer polynomials in $d$. Here is a complete executable proof of the finite identities. It multiplies coefficient vectors directly, retaining the constant and every higher degree separately.

```python
def block(d, length):
    coefficients = [(1, 0)]
    for j in range(1, length + 1):
        product = [(0, 0)] * (len(coefficients) + 1)
        for k, (a, b) in enumerate(coefficients):
            x, y = product[k]
            product[k] = (x + a - d*j*b, y + b + j*a)
            x, y = product[k + 1]
            product[k + 1] = (x - d*length*b, y + length*a)
        coefficients = product
    return coefficients

for d in range(3, 256, 8):
    for length, modulus, constants in (
        (4, 8, {(0, 4)}),
        (8, 256, {(48, 64), (240, 192)}),
    ):
        residues = [(a % modulus, b % modulus) for a, b in block(d, length)]
        assert residues[0] in constants
        assert residues[1:] == [(0, 0)] * length
print("Verified all 32 residue classes and all polynomial coefficients.")
```

## Proof for all indices

Let $T(X)=C_8(X)/16$. Its real coordinate is odd and its imaginary coefficient is 4 modulo 8. Every nonconstant coefficient of $T$ is divisible by 16. Therefore $T(i+h)-T(i)\in16hR$.

The product $F_e(i)=\prod_{j=0}^{2^e-1}T(i+j)$ has odd real coordinate and imaginary coefficient of valuation $e+2$. For $e=0$ this follows from the constant pair. For the induction put $h=2^e$. Multiplying the shift congruences gives $F_e(i+h)\equiv F_e(i)\pmod{16h}$, hence $F_{e+1}(i)\equiv F_e(i)^2\pmod{2^{e+4}}$. If $F_e(i)=a+bw$, the square has odd real coordinate $a^2-db^2$ and imaginary coefficient $2ab$ of valuation $e+3$. The congruence preserves both conclusions.

For $s>0$, set $e=v_2(s)$. A product of $s$ normalized blocks consists of an odd number of length-$2^e$ runs. The real coordinate of each run is odd, and its imaginary coefficient is $2^{e+2}\pmod{2^{e+3}}$. In the product, every contribution involving at least two imaginary coefficients vanishes modulo $2^{e+3}$. The odd number of single contributions gives an imaginary coefficient of valuation $e+2$. Multiplying back by $16^s$ gives $v_2(B_{8s})=4s+2+v_2(s)$.

After extracting $4^m$ at index $4m$, the product reduces to $w^m\pmod2$ by the four-factor identity. Since $w^2=1\pmod2$, the next factor takes it to $1+w\pmod2$, and the following factor preserves that residue. This proves $v_2(B_{4m+1})=v_2(B_{4m+2})=2m$. If $m$ is odd we also get $v_2(B_{4m})=2m$. Finally,

$$ (1+d(4m)^2)B_{4m-1}=B_{4m}-4mA_{4m}. $$

The left multiplier is odd. The second term on the right is divisible by $2^{2m+2+v_2(m)}$, strictly above the established order of $B_{4m}$ for both parities of $m>0$. This gives $v_2(B_{4m-1})=v_2(B_{4m})$ and completes the table.

The fixed-$d=3$ proof includes a separate [million-index numerical check](./A363412TwoAdic.md). KitaKen1's [earlier Gaussian-integer proof](https://github.com/KitaKen1/oeis-a105751-two-adic/tree/a9692d90078c4dff1478acaaa70be2fba06a3ef9) concerns $d=1$, a different congruence class with a different valuation law.
