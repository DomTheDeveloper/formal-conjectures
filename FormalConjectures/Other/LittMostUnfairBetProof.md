# The most unfair Litt coin-word bet

## Exact proof certificate for the fair binary case

This note proves the finite extremal statement underlying the asymptotic
unfairness problem posed by Ekhad and Zeilberger.  It also records the exact
Walsh-energy lemma used by the companion Lean development.

The statement concerns the coefficient in the asymptotic expansion proved by
Janson, Nica, and Segert.  Their theorem gives, for distinct binary words
`A,B` of common length `ell`,

\[
\Pr(N_A(n)>N_B(n))-\Pr(N_B(n)>N_A(n))
 = \frac{\theta_{BB}-\theta_{AA}}{\sqrt{2\pi\sigma^2}}n^{-1/2}
   +O(n^{-1}),
\]

with

\[
\sigma^2=2^{1-\ell}
  \bigl(1+\theta_{AA}+\theta_{BB}-\theta_{AB}-\theta_{BA}\bigr).
\]

Thus the finite optimization problem is to maximize

\[
F(A,B)=
\frac{|\theta_{AA}-\theta_{BB}|}
{\sqrt{1+\theta_{AA}+\theta_{BB}-\theta_{AB}-\theta_{BA}}}.
\]

For words `U,V`, put

\[
\theta_{UV}=\sum_{\substack{1\le r\le \ell-1\\
\operatorname{suffix}_r(U)=\operatorname{prefix}_r(V)}}2^{r-\ell}.
\]

Write

\[
a=\theta_{AA},\quad b=\theta_{BB},\quad
c=\theta_{AB},\quad d=\theta_{BA},\quad
D=1+a+b-c-d,
\]

and

\[
M=\sum_{r=1}^{\ell-1}2^{r-\ell}=1-2^{1-\ell}.
\]

## The theorem

For every integer `ell >= 2`,

\[
\max_{A\ne B} F(A,B)=M.
\]

The maximizers are exactly, up to complementing every letter, reversing both
words, and swapping `A` and `B`,

\[
H^{\ell-1}T\quad\text{and}\quad H^\ell.
\]

Consequently the largest leading asymptotic unfairness is

\[
\frac{2^{(\ell-2)/2}(1-2^{1-\ell})}{\sqrt{\pi n}}.
\]

## 1. The candidate pair

Let

\[
A=H^{\ell-1}T,\qquad B=H^\ell.
\]

The word `A` has no proper border, while every proper prefix of `B` is also a
suffix.  Moreover `A` has no suffix equal to a prefix of `B`, whereas every
proper suffix of `B` equals the corresponding prefix of `A`.  Hence

\[
a=0,\qquad b=M,\qquad c=0,\qquad d=M.
\]

Therefore `D=1` and `F(A,B)=M`.

## 2. Any pair containing a constant word

By complement symmetry it is enough to take `B=H^ell`.  Let `p` and `s` be
the lengths of the initial and terminal runs of `H` in `A`.  Since `A` is not
constant,

\[
p+s\le \ell-1.
\]

The cross-overlap sums are

\[
d=\sum_{r=1}^{p}2^{r-\ell},\qquad
c=\sum_{r=1}^{s}2^{r-\ell}.
\]

For nonnegative `p,s`,

\[
(2^p-1)(2^s-1)\ge0
\]

is equivalent to

\[
2^{p+1}+2^{s+1}\le 2^{p+s+1}+2.
\]

Using `p+s <= ell-1` and subtracting `4`, this gives

\[
\sum_{r=1}^{p}2^r+\sum_{r=1}^{s}2^r
\le \sum_{r=1}^{\ell-1}2^r.
\]

Thus `c+d <= M`, so

\[
D=1+a+M-c-d\ge1+a\ge1.
\]

Also `0 <= a <= M`, whence

\[
F(A,H^\ell)=\frac{M-a}{\sqrt D}\le M.
\]

For equality, necessarily `a=0`, `D=1`, and `c+d=M`.  Equality in the power
inequality requires both `p+s=ell-1` and `(2^p-1)(2^s-1)=0`.  Therefore
`(p,s)=(ell-1,0)` or `(0,ell-1)`, giving exactly
`H^{ell-1}T` or `TH^{ell-1}`.

## 3. Walsh translation-shape identity

Encode `H,T` by signs `+1,-1`.  Write the two words as

\[
A=(a_0,\ldots,a_{\ell-1}),\qquad
B=(b_0,\ldots,b_{\ell-1}).
\]

For a finite coordinate set `S`, let

\[
a_S=\prod_{i\in S}a_i,\qquad b_S=\prod_{i\in S}b_i.
\]

The difference of the two cylinder indicators has Walsh expansion

\[
1_A(x)-1_B(x)=2^{-\ell}
\sum_{\varnothing\ne S\subseteq\{0,\ldots,\ell-1\}}
(a_S-b_S)x_S.
\]

Normalize every nonempty set by translating its minimum to `0`.  For a
normalized translation shape `T`, define

\[
m_T=\frac12\sum_{t:\,T+t\subseteq\{0,\ldots,\ell-1\}}
(a_{T+t}-b_{T+t}).
\]

When the difference of occurrence counts is written as a sum over consecutive
windows, equal global Walsh monomials arise exactly from translates belonging
to the same shape.  Distinct global monomials are orthogonal.  Boundary terms
are `O(1)`, so division by the number of windows gives the long-run variance

\[
\sigma^2=4^{1-\ell}\sum_T m_T^2.
\]

Comparing with the overlap formula for `sigma^2` yields the exact identity

\[
D=2^{1-\ell}\sum_Tm_T^2. \tag{1}
\]

This identity also makes positivity and the reversal-degenerate zero-variance
cases transparent.

## 4. Exact variance-gap lemma

### Lemma

For two nonconstant words `A,B` of length `ell >= 2`, either

\[
\theta_{AA}=\theta_{BB},
\]

or

\[
D\ge\frac14.
\]

### Proof

Put `q_i=a_i b_i`.  A one-translation shape `S` has `m_S^2=1` precisely when

\[
\prod_{i\in S}q_i=-1.
\]

#### Case 1: an interior disagreement

Assume `q_j=-1` for some `1 <= j <= ell-2`.  Consider all full-span shapes

\[
S_R=\{0,\ell-1\}\cup R,\qquad
R\subseteq\{1,\ldots,\ell-2\}.
\]

Each has only the translation `t=0`.  Toggling the chosen disagreeing
coordinate `j` is a fixed-point-free involution on the choices of `R` and
reverses the sign of `prod_{i in S_R} q_i`.  Hence exactly half of the
`2^{ell-2}` choices have a nonzero coefficient.  Therefore

\[
\sum_Tm_T^2\ge2^{\ell-3},
\]

and (1) gives `D >= 1/4`.

#### Case 2: the words agree at every interior coordinate

If they differ at exactly one endpoint, every full-span shape above has a
nonzero unit coefficient.  This gives the stronger bound `D >= 1/2`.

If they differ at neither endpoint, then `A=B`, so their self-overlap sums are
equal.

It remains to treat the case in which both endpoints differ.  For `ell=2`,
the only two nonconstant words are reversals of one another and have equal
self-overlap sums.  Assume now `ell >= 3`.

For every

\[
R\subseteq\{1,\ldots,\ell-3\},
\]

use the span-`ell-2` shape

\[
T_R=\{0,\ell-2\}\cup R.
\]

It has exactly two translations.  Since one translated set contains only the
left differing endpoint and the other contains only the right differing
endpoint,

\[
m_{T_R}=a_{T_R}+a_{T_R+1}.
\]

Thus its square is `4` exactly when

\[
a_{T_R}a_{T_R+1}=1. \tag{2}
\]

Expanding the left side gives

\[
a_0a_1a_{\ell-2}a_{\ell-1}
\prod_{i\in R}(a_i a_{i+1}). \tag{3}
\]

If some interior adjacency `a_i a_{i+1}` with `1 <= i <= ell-3` equals `-1`,
toggling that `i` balances the choices of `R`.  Exactly `2^{ell-4}` shapes
then satisfy (2), and their square contribution is

\[
4\cdot2^{\ell-4}=2^{\ell-2}\ge2^{\ell-3}.
\]

Otherwise the common interior of the two words is constant.  Expression (3)
reduces to `a_0 a_{ell-1}`.  If the endpoints of `A` are equal, every one of
the `2^{ell-3}` shapes contributes `4`, again more than enough.  If its
endpoints are opposite, then flipping both endpoints turns `A` into its
reversal.  Thus `B=reverse(A)`.  Reversal preserves every proper border, so
`theta_AA=theta_BB`.

This exhausts all cases and proves the lemma.

## 5. Two nonconstant words are strictly suboptimal

A border of length `ell-1` would imply

\[
w_0w_1\cdots w_{\ell-2}=w_1w_2\cdots w_{\ell-1},
\]

and hence all adjacent letters are equal.  Therefore a nonconstant word has
no border of length `ell-1`, and

\[
\theta_{WW}\le\sum_{r=1}^{\ell-2}2^{r-\ell}=M-\frac12.
\]

For two nonconstant words,

\[
|a-b|\le M-\frac12.
\]

If `a=b`, their leading unfairness is zero.  Otherwise the variance-gap lemma
gives `D >= 1/4`, and therefore

\[
F(A,B)\le2\left(M-\frac12\right)=2M-1<M,
\]

because `M<1`.

Combining this strict inequality with the constant-word analysis proves the
theorem and the complete equality classification.

## 6. Integer-cleared form used in Lean

Let

\[
S(U,V)=\sum_{\substack{1\le r\le\ell-1\\
\operatorname{suffix}_r(U)=\operatorname{prefix}_r(V)}}2^r.
\]

Then `theta_UV=S(U,V)/2^ell`.  Put

\[
\Delta=|S(A,A)-S(B,B)|,
\]

and

\[
Q=2^\ell+S(A,A)+S(B,B)-S(A,B)-S(B,A).
\]

The desired inequality `F(A,B) <= M` is equivalent, with no division or
square roots, to

\[
\Delta^2 2^\ell\le(2^\ell-2)^2Q. \tag{4}
\]

For a constant-word pair, `Delta <= 2^ell-2` and `Q >= 2^ell`.  For two
nonconstant words, either `Delta=0`, or

\[
\Delta\le2^{\ell-1}-2,\qquad Q\ge2^{\ell-2}.
\]

These bounds imply (4) by elementary natural-number arithmetic.  The
candidate pair has

\[
\Delta=2^\ell-2,\qquad Q=2^\ell,
\]

so equality holds.

## References

- Ekhad and Zeilberger, “How to Answer Questions of the Type: If you toss a
  coin n times, how likely is HH to show up more than HT?” and the associated
  challenge page.
- Svante Janson, Mihai Nica, and Simon Segert, “The probability of competing
  binomial pattern counts,” arXiv:2503.19035 / Journal of Theoretical
  Probability (2025).
