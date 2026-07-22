# BMO #8 positive solution

For the recurrence beginning at `(a₀, b₀) = (10, 12)`, exact iteration reaches

```text
(a₁₂₁₀₆₈₂, b₁₂₁₀₆₈₂) = (1749056, 3498111).
```

Therefore

```text
1749056 = 3498111 / 2 + 1
```

with natural-number division. The Lean proof in
`FormalConjectures/Other/BeaverMathOlympiad8Proof.lean` uses a tail-recursive evaluator,
proves uniqueness of every sequence satisfying the stated recurrence, and checks the witness with
`native_decide`.
