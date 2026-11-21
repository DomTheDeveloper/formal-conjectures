# The analytic step in the Riemann hypothesis proof

[OriginalReflection.lean](OriginalReflection.lean) contains the two original Lean proofs in the shortened module and the definition of their assumption. They compile using two Mathlib imports. The first proof takes the trivial Dirichlet character of modulus one. Its L-function is the Riemann zeta function. The second proof applies the functional equation to reflect a zero on the left of the critical line to a zero on the right. Its gamma-factor check excludes the negative even integers.

[ZetaReflection.lean](ZetaReflection.lean) proves a sharper statement of what this argument needs. Ordinary RH is equivalent to zeta having no zero with real part strictly between one half and one and imaginary part greater than or equal to zero. Complex conjugation supplies the lower half of the strip. Mathlib supplies nonvanishing on and to the right of the line with real part one. Proving the remaining zero-free region is the arithmetic problem.

Both files use Lean 4.33.1 and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. To check them from an existing checkout with that Mathlib environment, supply its location to the script below. The script runs stock Lean on both files, rejects warnings, checks the axiom list, and replays their compiled declarations with `leanchecker`.

```bash
bash _certificates/RiemannReduction/analytic-reflection/check.sh /path/to/pinned/mathlib/project
```

The [complete reduced source](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44958217634/artifacts/14727848302) retains the original unconditional theorems. The two small files here explain the final analytic step.
