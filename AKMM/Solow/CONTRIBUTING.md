# Contributing

Contributions of fixes, examples, and clearer statements are welcome. Submit
only work you have the right to contribute. Original contributions are
accepted under the repository's Apache License 2.0. Identify any third-party
material and preserve its notices.

Every Lean file starts with the Apache copyright header that Mathlib's header
linter checks. State domains and assumptions explicitly, including the ones the
literature leaves implicit. Do not use proof placeholders or add axioms.

Run `python scripts/verify.py`: it builds the complete library, freshly
recompiles every contributed theorem, and checks its axiom dependencies. For
new modules or theorems, update `proof-manifest.json` and the README library
map in the same commit. Keep `docs/source-map.md` accurate: every result from
the literature that is formalised appears there with its Lean name, and every
place where the Lean statement departs from the published one is recorded in
`docs/corrections.md`.
