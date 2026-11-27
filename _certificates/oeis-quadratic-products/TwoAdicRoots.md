# Two of Bala's valuation conjectures reduce to two explicit 2-adic integers

For $d=3,5$ let $P_n=A_n+B_nw=\prod_{k=1}^n(1+kw)$, where $w^2=-d$. Set $v=v_2$ and use $v(0)=+\infty$ when discussing divisibility. The sequences below are the real coefficient for $d=3$ ([A363411](https://oeis.org/A363411)) and the imaginary coefficient for $d=5$ ([A363416](https://oeis.org/A363416)). Bala predicts slopes $1/2$ and $1/4$ respectively.

There are unique 2-adic integers $\alpha_3,\alpha_5$ defined below for which the following table holds. Here $n=8m+r$, $m\ge0$. In the row $r=0$ of the last column take $m\ge1$.

| $r$ | $v(A_{8m+r})$ for $d=3$ | $v(B_{8m+r})$ for $d=5$ |
|---|---|---|
| 0 | $4m$ | $2m+2+v(m)$ |
| 1, 2 | $4m$ | $2m$ |
| 3 | $4m+4+v(m-\alpha_3)$ | $2m+3+v(m-\alpha_5)$ |
| 4 | $4m+4+v(m+1+\alpha_3)$ | $2m+3+v(m+1+\alpha_5)$ |
| 5, 6 | $4m+2$ | $2m+1$ |
| 7 | $4m+4$ | $2m+4+v(m+1)$ |

The residues modulo 4096 are $\alpha_3\equiv3198$ and $\alpha_5\equiv1357$. The finite program at the end computes each residue from the original products. The proof below constructs all of their digits.

On each of the two exceptional residue classes, the extra term has an exact geometric distribution. For every $k\ge0$, divisibility by $2^k$ selects exactly one residue of $m$ modulo $2^k$. Equality of the extra valuation to $k$ therefore has natural density $2^{-k-1}$ inside that class. For either sequence the conjectured slope holds on a set of natural density one. For each $\varepsilon>0$ at most $O_\varepsilon(\log(2N))$ positive indices $n\le N$ deviate from the predicted valuation by at least $\varepsilon n$. More explicitly, apart from at most $2(1+\lfloor\log_2 N\rfloor)$ indices up to $N$, the absolute error is at most $\log_2(n+2)+10$. The ordinary all-index limits remain open here.

## Eight-factor products

Put $s=4$ for $d=3$ and $s=2$ for $d=5$. For $0\le r<8$ define
$$
T_r(X)=2^{-s}\prod_{j=1}^8(1+(8X+r+j)w).
$$
For all eight offsets this is an integer polynomial pair with odd real and even imaginary coordinate when evaluated at any integer. For $r=0,3,4$ every nonconstant coefficient is divisible by 16 and the constant imaginary coordinate is 4 modulo 8. These finite coefficient identities are checked directly by the program below. In particular $T_r(i+h)-T_r(i)\in16h\mathbb Z[w]$ for those three offsets.

For $r=0,3,4$ and $h>0$ write $\prod_{j=0}^{h-1} T_r(i+j)=C+Dw$. Then $C$ is odd and $v(D)=2+v(h)$, for every integer $i$. For length $h=1$ this follows from the constant pair. For length $2h$ with $h$ a power of two, the second half is the first half modulo $16h$. Squaring the first half produces imaginary coefficient $2CD$ of valuation $3+v(h)$, preserved by the error divisible by $16h$. For an odd number of equal dyadic runs each contributes its imaginary coefficient times odd real factors. Those contributions have the same residue modulo $2^{3+v(h)}$ where $2^{v(h)}$ is the run length. Terms with two or more imaginary factors are divisible by that modulus. This proves the claim for an arbitrary length $h$.

## The two exceptional classes

Fix $r=3$ or $4$. Set $c=2$ for $d=3$, $c=1$ for $d=5$, and let $Z_m=P_{8m+r}/2^{sm+c}$. For $m\ge0$ this is integral by the recurrence $Z_{m+1}=Z_mT_r(m)$. For $d=3$ the imaginary coordinate of $Z_0$ is odd and the real coordinate is divisible by 4. For $d=5$ the real coordinate is odd and the imaginary coordinate is divisible by 4. These conditions persist under multiplication by $T_r(m)$.

In $\mathbb Z_2$ divide the exceptional coordinate by the odd coordinate and call the quotient $u_m$. Then $F_r(m)=u_m/4$ is integral. For $h>0$, the product $C+Dw$ above changes the quotient as follows.

| Parameter | $u_{m+h}$ | $u_{m+h}-u_m$ |
|---|---|---|
| $d=3$ (real over imaginary) | $(Cu_m-dD)/(C+Du_m)$ | $-(d+u_m^2)D/(C+Du_m)$ |
| $d=5$ (imaginary over real) | $(D+Cu_m)/(C-dDu_m)$ | $(1+du_m^2)D/(C-dDu_m)$ |

The factors multiplying $D$ are units. Thus $v(F_r(m+h)-F_r(m))=v(h)$. In particular $F_r$ induces an injective map on each finite ring $\mathbb Z/2^k\mathbb Z$, hence a bijection there. The unique preimages of zero are compatible in $k$ and define $\alpha_{d,r}\in\mathbb Z_2$. For every $m\ge0$ we obtain $v(F_r(m))=v(m-\alpha_{d,r})$, including a possible infinite value.

There is one such constant per sequence after reflection. Define the rational product at negative indices by extending $P_n=P_{n-1}(1+nw)$ backwards from $P_0=1$. For $n\ge0$ this gives $P_{-n-1}=\overline{P_n}^{-1}=P_n/(A_n^2+dB_n^2)$. Both coordinate quotients are unchanged by this scalar. Every $T_r(i)$ at an integer $i$ has odd norm and is a unit over $\mathbb Z_2$. Backwards iteration therefore extends the same quotient and the same isometry to all integer indices $m$. In particular $F_3(m)=F_4(-m-1)$ (the subscripts here are offsets). This gives $\alpha_{d,4}=-1-\alpha_{d,3}$. Taking $\alpha_d=\alpha_{d,3}$ gives the exceptional rows of the table.

## Other indices and convergence

For fixed $r$, every factor $T_r(i)$ reduces to $(1,0)$ modulo 2. Thus after extracting $2^{sm}$ from $P_{8m+r}$, the first odd coordinate of the normalized prefix $P_r$ stays odd. Applying this to the explicit prefixes proves the ordinary rows in the $d=3$ column and the rows $r=1,2,5,6$ for $d=5$. For $d=5$, the block assertion at offset zero gives $v(B_{8m})=2m+2+v(m)$ and $v(A_{8m})=2m$. With $k=8m$ the identity
$$
(1+5k^2) B_{k-1}=B_k-kA_k
$$
gives $v(B_{k-1})=v(B_k)$ since $v(kA_k)=v(B_k)+1$. This proves the last row. At most one zero can occur per exceptional residue class by injectivity.

For either exceptional class, a deviation of at least $\varepsilon n$ in $M\le n<2M$ with $M$ sufficiently large forces its extra valuation to be at least $\lfloor\varepsilon M\rfloor-8$. This selects one residue modulo a power of two greater than $2M$ for large $M$, hence at most one index per exceptional class in that interval. The ordinary rows have at most logarithmic errors. Summing over dyadic intervals proves the stated bound. For the explicit version, the ordinary rows always have error at most $\log_2(n+2)+10$. On either exceptional row the error is the extra valuation plus a constant of absolute value at most three. If the error exceeds that threshold, the extra valuation exceeds $\log_2(M+2)+7$, so all such $m$ occupy a single residue modulo a power of two larger than $2M$. At most two indices per dyadic interval can exceed the threshold. Equivalently, the missing all-index conclusion for each sequence reduces to proving $v(m-\alpha_d)=o(m)$ and $v(m+1+\alpha_d)=o(m)$ as $m\to\infty$ (finite initial zeros have no effect).

## Exponential spacing of linear-sized errors

There is a sharper bound for a fixed relative tolerance. Fix $\varepsilon>0$ and one exceptional class $r\in\{3,4\}$. Suppose $n_1<n_2$ are in that class and at each index the absolute error from the predicted linear valuation is at least $\varepsilon n_i$. Write $n_i=8m_i+r$. By the table, $m_i$ is within $2$-adic valuation at least $\lfloor\varepsilon n_1\rfloor-3$ of the same root. Thus
$
 n_2-n_1\ \ge\ 8\cdot 2^{\max(0,\lfloor\varepsilon n_1\rfloor-3)}.
$
In particular $n_2\ge 2^{\varepsilon n_1-1}$ for sufficiently large $n_1$. Put $x_i=\varepsilon n_i/4$. Above a fixed threshold depending only on $\varepsilon$, this implies $x_2\ge 2^{x_1}$. Consequently, for either sequence the number of errors of size at least $\varepsilon n$ up to $N$ is $O_\varepsilon(1+\log^* N)$. Here $\log^* N$ counts the number of base-two logarithms required to reach a value at most one. The two exceptional classes each satisfy this spacing bound. The ordinary classes have only finitely many errors of the indicated size.

An [independent recurrence scan](./CheckTwoAdicRoots.py) found zero errors larger than $\log_2(n+2)+10$ among the first million positive indices of either sequence. The maximum absolute errors over this range were $41/2$ at $n=451571$ for A363411 and $93/4$ at $n=666219$ for A363416.

## Reproducible checks

The certificate verifies the polynomial hypotheses for every offset and both parameters, calculates the two roots modulo 4096 by enumeration, and compares all 65,536 residue-table predictions with independent normalized finite products up to the tested precision. It uses the Python standard library.

```python
def mul(d, x, y):
    a, b = x
    c, f = y
    return a*c-d*b*f, a*f+b*c

def product(d, start, length):
    z = (1,0)
    for j in range(start, start+length):
        z = mul(d, z, (1,j))
    return z

def polynomial(d, r):
    coefficients = [(1,0)]
    for j in range(r+1, r+9):
        nxt = [(0,0)]*(len(coefficients)+1)
        for i,(a,b) in enumerate(coefficients):
            x,y = nxt[i]
            nxt[i] = (x+a-d*j*b, y+b+j*a)
            x,y = nxt[i+1]
            nxt[i+1] = (x-8*d*b, y+8*a)
        coefficients = nxt
    return coefficients

def finite_order(x, bits):
    x %= 1 << bits
    return bits if not x else (x & -x).bit_length()-1

def divide(z, exponent):
    scale = 1 << exponent
    assert all(t % scale == 0 for t in z)
    return tuple(t//scale for t in z)

bits = 12
for d,s,c,target,root in [(3,4,2,0,3198),(5,2,1,1,1357)]:
    for r in range(8):
        coeff = [divide(pair,s) for pair in polynomial(d,r)]
        assert (coeff[0][0]%2,coeff[0][1]%2) == (1,0)
        assert all(a%2==b%2==0 for a,b in coeff[1:])
        if r in (0,3,4):
            assert coeff[0][1]%8 == 4
            assert all(a%16==b%16==0 for a,b in coeff[1:])
    for r in (3,4):
        z = divide(product(d,1,r), c)
        hits = []
        for m in range(1 << bits):
            assert z[1-target]%2 and z[target]%4==0
            if z[target] % (1 << (bits+2)) == 0:
                hits.append(m)
            t = divide(product(d,8*m+r+1,8), s)
            z = tuple(x%(1 << (bits+2)) for x in mul(d,z,t))
        assert hits == [(root if r==3 else -1-root)%(1 << bits)]
    # Run sequential products from the start, including all eight offsets.
    prec = bits+8
    modulus = 1 << prec
    z = (1,0)
    for m in range(1 << bits):
        current = z
        for r in range(8):
            val = finite_order(current[target],prec)
            if r in (3,4):
                extra = finite_order(m-root if r==3 else m+1+root,bits)
                assert min(val,c+2+bits) == c+2+extra
            elif d==3:
                assert val == (0 if r in (0,1,2) else 4 if r==7 else 2)
            elif r==0 and m:
                assert val == 2+finite_order(m,prec)
            elif r==0:
                assert current[target] == 0
            elif r==7:
                assert val == 4+finite_order(m+1,prec)
            elif r:
                assert val == int(r in (5,6))
            current = mul(d,current,(1,8*m+r+1))
        t = divide(product(d,8*m+1,8), s)
        z = tuple(x%modulus for x in mul(d,z,t))
print("Verified polynomial identities, both root pairs, and 65,536 table entries.")
```
