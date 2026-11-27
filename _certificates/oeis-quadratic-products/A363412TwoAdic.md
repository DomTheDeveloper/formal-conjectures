# Exact 2-adic valuation of every positive term of OEIS A363412

Peter Bala's [A363412](https://oeis.org/A363412) predicts $v_2(B_n)\sim n/2$, where $A_n+B_n w=\prod_{k=1}^n(1+kw)$ and $w^2=-3$. Write $v_2(x)$ for the exponent of 2 in a nonzero integer.

**Theorem.** For $m\ge0$,
$$v_2(B_{4m+1})=v_2(B_{4m+2})=2m.$$
For $m\ge1$,
$$v_2(B_{4m-1})=v_2(B_{4m})=
\begin{cases}2m & m\text{ odd},\\2m+1+v_2(m)&m\text{ even}.\end{cases}$$
Thus $v_2(B_n)=n/2+O(\log(2n))$ for all $n\ge1$. This proves the stated 2-adic limit.

### Two finite polynomial identities

All congruences of quadratic integers below are coordinatewise. In $R=\mathbb Z[w]/(w^2+3)$ put $C_h(X)=\prod_{j=1}^h(1+(hX+j)w)$. In the polynomial ring $R[X]$,
$$C_4(X)\equiv4w\pmod 8,\qquad C_8(X)\equiv240+192w\pmod{256}.$$
These are coefficientwise identities. For a reproducible expansion start with $(1,0)$, and for each factor with $k=hX+j$ replace $(a,b)$ by $(a-3kb,b+ka)$. The resulting lists of coefficient pairs in ascending degree are $[(0,4),(0,0),(0,0),(0,0),(0,0)]$ modulo 8 and $[(240,192),(0,0),\ldots,(0,0)]$ modulo 256, with eight zero pairs in the second list. The exact polynomial arithmetic is also supplied below.

In particular $C_4(X)/4\in R[X]$ reduces to $w$ modulo two. Also $T(X)=C_8(X)/16\in R[X]$ is a constant plus $16$ times a polynomial over $R$. Its real coordinate is odd and its imaginary coefficient is 4 modulo 8. For all integers $i,h$,
$$T(i+h)-T(i)\in16hR.$$

### Doubling eight-factor blocks

For $e\ge0$ let $F_e(i)=\prod_{j=0}^{2^e-1}T(i+j)$. We claim its real coordinate is odd and its imaginary coefficient has valuation exactly $e+2$, for every nonnegative starting index $i$. The case $e=0$ follows from the polynomial identity. Set $h=2^e$. By multiplying the factorwise shift congruences, $F_e(i+h)\equiv F_e(i)\pmod{16h}$. Hence
$$F_{e+1}(i)=F_e(i)F_e(i+h)\equiv F_e(i)^2\pmod{2^{e+4}}.$$
If $F_e(i)=a+bw$, the square has odd real coordinate $a^2-3b^2$ and imaginary coefficient $2ab$ of valuation $e+3$. An error divisible by $2^{e+4}$ preserves both conclusions. This proves the induction.

For any $s\ge1$, put $e=v_2(s)$. A length-$s$ product of the $T(i)$ consists of an odd number of length-$2^e$ blocks. Each has odd real coordinate and imaginary coefficient congruent to $2^{e+2}$ modulo $2^{e+3}$. In their product, the terms using exactly one imaginary coefficient each contribute $2^{e+2}$ modulo $2^{e+3}$ to the imaginary coefficient. Terms using at least two imaginary coefficients vanish modulo $2^{e+3}$. There are an odd number of the one-coefficient terms. Restoring the removed factor $16^s$ gives
$$v_2(B_{8s})=4s+2+v_2(s).$$

### The remaining indices

Put $Q_m=(A_{4m}+B_{4m}w)/4^m$. Since each normalized four-block reduces to $w$, $Q_m\equiv w^m\pmod2$. If $m$ is odd this gives $v_2(B_{4m})=2m$; for even $m=2s>0$ use the eight-block identity just proved. It also gives $2^{2m}\mid A_{4m}$ for all $m$.

Modulo two, $w^2=1$. Multiplying $w^m$ by the next factor $1+(4m+1)w$ therefore gives $1+w$ for either parity of $m$. The following even-indexed factor is 1 modulo two. This gives both formulas at $4m+1$ and $4m+2$.

Finally, multiplication by the conjugate of the last factor gives
$$(1+3(4m)^2)B_{4m-1}=B_{4m}-4mA_{4m}.$$
The left multiplier is odd. The term $4mA_{4m}$ is divisible by $2^{2m+2+v_2(m)}$, strictly above the known valuation of $B_{4m}$ for either parity of $m$. The valuation is therefore unchanged at $4m-1$. Since $v_2(m)\le\log_2 m$, the displayed exact formulas imply the limit over every positive index.

### Prior work and checks

The earlier [trureturing dossier](https://www.trureturing.org/research/bala3634-valuations/) records proofs of two 3-adic assertions for this sequence and related results for A363411. Here the target is the separate 2-adic slope in the OEIS COMMENTS. No exhaustive priority claim is made.

The following standard Python program verifies both polynomial identities and independently tests the closed formula at every index through one million. It computes the first thousand terms directly as integers. For the rest it retains normalized coordinates modulo a power of two exceeding the valuation precision needed in each four-block. A zero residue aborts the check.

```python
def v2(n):
    assert n
    return (n & -n).bit_length()-1

def times(x,y):
    a,b=x
    c,d=y
    return a*c-3*b*d, a*d+b*c

def polynomial_block(h):
    # Coefficients, in increasing degree, of the product at offsets hX+j.
    coeff=[(1,0)]
    for j in range(1,h+1):
        old = coeff
        coeff = [(0,0) for _ in range(len(old)+1)]
        for i,z in enumerate(old):
            for degree,factor in ((i,(1,j)),(i+1,(0,h))):
                u,v=times(z,factor)
                a,b=coeff[degree]
                coeff[degree]=(a+u,b+v)
    return coeff

for h,modulus,expected in ((4,8,(0,4)),(8,256,(240,192))):
    residues=[(a%modulus,b%modulus) for a,b in polynomial_block(h)]
    assert residues == [expected]+[(0,0)]*h

def predicted(n):
    if n%4 in (1,2):
        return 2*(n//4)
    m=(n+1)//4
    return 2*m+(0 if m%2 else 1+v2(m))

def check(bound):
    assert bound%4 == 0
    modulus = 1 << (bound.bit_length()+10)
    a,b=1,0
    direct=(1,0)
    for m in range(bound//4):
        block=(1,0)
        for j in range(1,5):
            n=4*m+j
            block=times(block,(1,n))
            c,d=times((a,b),block)
            observed=2*m+v2(d%modulus)
            assert observed == predicted(n)
            if n<=1000:
                direct=times(direct,(1,n))
                assert v2(direct[1]) == observed
        assert block[0]%4 == block[1]%4 == 0
        c,d=times((a,b),(block[0]//4,block[1]//4))
        a,b=c%modulus,d%modulus
    print("Verified both polynomial identities and all",bound,
          "valuation predictions. Final valuation:",observed)

check(1_000_000)
```
