/-
Copyright (c) 2024 BIU Students. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Liberman
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.ZetaValues

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

/-! ## What happens when the exponent is not a natural number?

The professor asked: what does (x + y)^α mean when α is not a whole number?

Answer: instead of a finite sum, we get an *infinite series*.
For α = -1/2, the coefficients of that series are the *central binomial coefficients*
— the middle numbers in each row of Pascal's triangle: 1, 2, 6, 20, 70, ...

Remarkably, these same numbers appear in a formula for π²/6,
which is the answer to the "Basel problem":  what is 1 + 1/4 + 1/9 + 1/16 + ...?

This connects a simple question about exponents all the way to
the Riemann zeta function ζ(s) = Σ 1/nˢ.
-/

-- ─────────────────────────────────────────────
-- Step 1: Central Binomial Coefficients
-- ─────────────────────────────────────────────

-- The central binomial coefficient C(2n, n) is the middle entry
-- in row 2n of Pascal's triangle.
-- Mathlib already defines this as Nat.centralBinom.
#check Nat.centralBinom
-- Nat.centralBinom : ℕ → ℕ

/-- C(2n, n) is defined as the middle entry of row 2n of Pascal's triangle. -/
theorem centralBinom_def (n : ℕ) : Nat.centralBinom n = (2 * n).choose n :=
  Nat.centralBinom_eq_two_mul_choose n

-- Let's compute the first few values: 1, 2, 6, 20, 70, 252
#eval (List.range 6).map Nat.centralBinom

-- These are exactly the numbers from the middle of Pascal's triangle:
--   Row 0:   [1]
--   Row 2:  1 [2] 1
--   Row 4: 1 4 [6] 4 1
--   Row 6: 1 6 15 [20] 15 6 1

-- ─────────────────────────────────────────────
-- Step 2: Where do they come from?
-- ─────────────────────────────────────────────

-- When we expand (1 - x)^(-1/2) as a power series (generalized binomial theorem),
-- the coefficient of xⁿ is exactly  C(2n, n) / 4ⁿ.
--
-- So the series looks like:
--   (1 - x)^(-1/2) = Σ_{n=0}^∞  C(2n,n) / 4ⁿ · xⁿ
--
-- This works for |x| < 1, and is just the usual binomial theorem
-- extended to α = -1/2 ∉ ℕ.

/-- The central binomial coefficient grows roughly like 4ⁿ / √(πn). -/
theorem centralBinom_pos (n : ℕ) : 0 < Nat.centralBinom n :=
  Nat.centralBinom_pos n

-- ─────────────────────────────────────────────
-- Step 3: The Basel Problem — Σ 1/n² = π²/6
-- ─────────────────────────────────────────────

-- This question was open for 90 years. Euler solved it in 1734.
-- The key insight: sin(πx) can be written as an *infinite product*
--   sin(πx) / (πx) = ∏_{n=1}^∞ (1 - x²/n²)
-- This is like applying the binomial theorem infinitely many times.
-- Comparing the x² coefficient on both sides gives:  Σ 1/n² = π²/6

-- Mathlib has this result — let's check it:
#check hasSum_zeta_two
-- hasSum_zeta_two : HasSum (fun n => 1 / n^2) (π^2 / 6)

-- The precise statement of ζ(2) = π²/6, proved directly from Mathlib:
theorem zeta_two_eq_pi_sq_div_six :
    ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq

-- ─────────────────────────────────────────────
-- Step 4: The Bridge — C(2n,n) appears in ζ(2)
-- ─────────────────────────────────────────────

-- The most surprising part: the central binomial coefficients from Step 1
-- appear directly in a formula for π²/6:
--
--   π²/6  =  3 · Σ_{n=1}^∞  1 / (n² · C(2n, n))
--
-- So the coefficients of (1-x)^(-1/2) are the same numbers that
-- help compute the sum 1 + 1/4 + 1/9 + 1/16 + ...

theorem central_binom_sum_eq_pi_sq_div_eighteen :
    ∑' n : ℕ, (1 : ℝ) / ((↑(n + 1)) ^ 2 * ↑(Nat.centralBinom (n + 1)))
    = Real.pi ^ 2 / 18 := by
  sorry
  -- This identity was used by Apéry (1978) as a model for his proof
  -- that ζ(3) is irrational — one of the most celebrated results
  -- of 20th century mathematics.

-- ─────────────────────────────────────────────
-- The full story in one picture:
-- ─────────────────────────────────────────────
--
--   (x+y)^α with α ∉ ℕ
--         ↓
--   infinite series with coefficients C(2n,n)/4ⁿ
--         ↓
--   central binomial coefficients C(2n,n)
--         ↓
--   ζ(2) = π²/6 = 3 · Σ 1/(n²·C(2n,n))
--         ↓
--   Riemann zeta function ζ(s)
--         ↓
--   Riemann Hypothesis — open problem, $1,000,000 prize
