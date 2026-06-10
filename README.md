# Binomial Theorem in Lean 4

This project formalizes the classical Binomial Theorem in Lean 4 using Mathlib.

## Contents

`BinomialTheorem/Basic.lean` contains:

* an explicit proof by induction of the Binomial Theorem;
* the identity stating that the sum of row `n` of Pascal's triangle is `2 ^ n`;
* the alternating-sum identity for positive rows.

`BinomialTheorem/GaussProofs.lean` contains elementary Lean exercises culminating in the
formula for the sum of the first `n` natural numbers.

`BinomialTheorem.lean` is the root module and imports both files.

## Building

The project uses Lean 4.30.0 and Mathlib.

Build the project with:

```sh
lake build
```
