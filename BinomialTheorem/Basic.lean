/-
Copyright (c) 2024 BIU Students. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Liberman
-/
import Mathlib.Data.Nat.Choose.Sum

/-! # Binomial Theorem

Formalization of the Binomial Theorem and its corollaries.
-/

open Finset BigOperators

-- The Binomial Theorem: (x + y)^n = Σ_{k=0}^{n} C(n,k) * x^k * y^(n-k)
#check @add_pow

/-- The Binomial Theorem holds for any commutative semiring. -/
theorem binomial_theorem {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ k ∈ range (n + 1), x ^ k * y ^ (n - k) * n.choose k :=
  add_pow x y n

/-- The sum of all binomial coefficients in row n equals 2 ^ n. -/
theorem sum_binomial_coeffs (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-- The alternating sum of binomial coefficients equals 0 for positive n. -/
theorem alternating_sum_binomial (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range (n + 1), ((-1) ^ k * n.choose k : ℤ)) = 0 :=
  Int.alternating_sum_range_choose_of_ne hn.ne'
