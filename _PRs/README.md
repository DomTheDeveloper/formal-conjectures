# Google DeepMind PR Queue

This directory separates work that is genuinely ready for an upstream Google DeepMind Formal Conjectures pull request from work that still needs correction or validation.

## Promotion rule

An item may enter `ready/` only when all of the following are true:

1. The formal statement matches the intended mathematical problem.
2. The exact Lean theorem compiles under the repository's pinned toolchain.
3. The proof contains no `sorry`, `admit`, `native_decide`, unsafe declarations, custom axioms, or compiler-trust shortcuts.
4. The exact theorem axiom audit contains no `sorryAx`.
5. The focused validation is green in ProofPlaygrond and in `DomTheDeveloper/formal-conjectures`.
6. The proposed upstream patch is focused, clean, and accompanied by a copy-paste PR description.

Items that fail any gate remain in `queue/` or `blocked/`.
