/-
Copyright (c) 2024 BIU Students. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Liberman, Nick Sokolovsky
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.ZetaValues

/-! # Binomial Theorem — From Pascal's Triangle to the Riemann Zeta Function

This file formalizes the Binomial Theorem and traces its surprising connections
all the way to the Riemann Zeta Function and Euler's famous result ζ(2) = π²/6.

The story:
  (x+y)^n  — a finite sum with binomial coefficients (Pascal's Triangle)
      ↓
  (1+x)^α for α ∉ ℕ  — an infinite series (Newton's generalization)
      ↓
  (1+x)^(-1) = 1/(1+x)  — the geometric series (α = -1)
      ↓
  -ln(1-x) = Σ xⁿ/n  — the logarithm appears via integration
      ↓
  Li₂(x) = Σ xⁿ/n²  — the dilogarithm (integrate again)
      ↓
  Liₛ(x) = Σ xⁿ/nˢ  — the polylogarithm family
      ↓
  ζ(s) = Liₛ(1) = Σ 1/nˢ  — the Riemann Zeta Function
      ↓
  ζ(2) = π²/6  — Euler's Basel result
-/

open Finset BigOperators Real

-- ─────────────────────────────────────────────
-- Part 1: The Classical Binomial Theorem
-- ─────────────────────────────────────────────

/-- The Binomial Theorem: (x + y)^n = Σ C(n,k) · x^k · y^(n-k)
    Holds for any commutative semiring — integers, reals, polynomials, etc. -/
theorem binomial_theorem {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ k ∈ range (n + 1), x ^ k * y ^ (n - k) * n.choose k :=
  add_pow x y n

/-- Substituting x = y = 1: the sum of all binomial coefficients in row n equals 2^n.
    This is the count of all subsets of an n-element set. -/
theorem sum_binomial_coeffs (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-- Substituting x = 1, y = -1: the alternating sum equals 0 for positive n.
    Even- and odd-positioned entries in Pascal's Triangle are perfectly balanced. -/
theorem alternating_sum_binomial (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range (n + 1), ((-1) ^ k * n.choose k : ℤ)) = 0 :=
  Int.alternating_sum_range_choose_of_ne hn.ne'

-- ─────────────────────────────────────────────
-- Part 2: Newton's Generalized Binomial Theorem
-- ─────────────────────────────────────────────

/-!
What happens when the exponent α is not a natural number?

Newton discovered that we can still write an infinite series:

  (1 + x)^α = 1 + α·x + α(α-1)/2! · x² + α(α-1)(α-2)/3! · x³ + ...

This converges for |x| < 1.  Key examples:
  α = 1/2  →  (1+x)^(1/2)  = 1 + ½x - ⅛x² + ...
  α = -1/2 →  (1+x)^(-1/2) = 1 - ½x + ³⁄₈x² - ...
  α = -1   →  (1+x)^(-1)   = 1 - x + x² - x³ + ...  (geometric series!)

We use this as a known result (as in the slides: "we used as a known result").
-/

/-- The generalized binomial coefficient for real exponent α and order k -/
noncomputable def generalizedBinomCoeff (α : ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ range k, (α - (i : ℝ))) / (k.factorial : ℝ)

-- ─────────────────────────────────────────────
-- Part 3: α = -1 — The Geometric Series
-- ─────────────────────────────────────────────

/-!
Setting α = -1 in Newton's formula:
  (1 + x)^(-1) = 1 - x + x² - x³ + ...

Substituting -x for x gives the geometric series:
  1/(1-x) = 1 + x + x² + x³ + ...  for |x| < 1

The signs alternate because C(-1, k) = (-1)^k.
This is the starting point for the journey to the Riemann Zeta Function.
-/

/-- The geometric series: 1/(1-x) = Σₙ xⁿ, valid for ‖x‖ < 1.
    This is the α = -1 case of Newton's Generalized Binomial Theorem. -/
theorem geometric_series (x : ℝ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => x ^ n) (1 - x)⁻¹ :=
  hasSum_geometric_of_norm_lt_one hx

-- ─────────────────────────────────────────────
-- Part 4: Integration — The Logarithm Appears
-- ─────────────────────────────────────────────

/-!
Integrating the geometric series term by term from 0 to x:

  ∫₀ˣ 1/(1-t) dt  =  ∫₀ˣ Σₙ tⁿ dt  =  Σₙ₌₁ xⁿ/n

Left side: -ln(1-x)

So:  -ln(1-x) = x + x²/2 + x³/3 + ...  for |x| < 1

This is the first time we see 1/n — the harmonic structure of the logarithm.
-/

/-- The logarithm series: -ln(1-x) = Σₙ₌₁ xⁿ/n, for |x| < 1.
    Obtained by integrating the geometric series term by term. -/
theorem log_series (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 - x)) :=
  Real.hasSum_pow_div_log_of_abs_lt_one hx

-- ─────────────────────────────────────────────
-- Part 5: The Polylogarithm Family
-- ─────────────────────────────────────────────

/-!
Dividing the log series by x and integrating again produces:

  Li₂(x) = Σₙ₌₁ xⁿ/n²   (the dilogarithm)

Repeating the process gives the polylogarithm family:

  Li₁(x) = Σₙ₌₁ xⁿ/n     = -ln(1-x)
  Li₂(x) = Σₙ₌₁ xⁿ/n²    (dilogarithm)
  Li₃(x) = Σₙ₌₁ xⁿ/n³
  Liₛ(x) = Σₙ₌₁ xⁿ/nˢ

Every integration raises the power in the denominator by 1.
A whole family of special functions emerges naturally from repeated integration.
-/

/-- The polylogarithm: Liₛ(x) = Σₙ₌₁ xⁿ/nˢ -/
noncomputable def polylogarithm (s : ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ s

-- ─────────────────────────────────────────────
-- Part 6: The Riemann Zeta Function
-- ─────────────────────────────────────────────

/-!
Setting x = 1 in the polylogarithm:

  Liₛ(1) = Σₙ₌₁ 1/nˢ = ζ(s)

This is the Riemann Zeta Function!

For s = 2 (Euler's Basel problem, solved 1734):
  ζ(2) = 1 + 1/4 + 1/9 + 1/16 + ... = π²/6

Mathematical Genealogy:
  Binomial Theorem → 1/(1-x) → Σxⁿ → Σxⁿ/n → Σxⁿ/n² → ζ(2) = π²/6

A theorem about algebraic expansion leads to one of the deepest constants
in mathematics.  From Pascal's Triangle to Analytic Number Theory.
-/

/-- The Riemann Zeta Function: ζ(s) = Σₙ₌₁ 1/nˢ (for s > 1) -/
noncomputable def zetaFunction (s : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s

/-- The polylogarithm evaluated at x = 1 equals the zeta function -/
theorem polylog_at_one_eq_zeta (s : ℝ) :
    polylogarithm s 1 = zetaFunction s := by
  simp [polylogarithm, zetaFunction]

/-- Euler's Basel Problem: ζ(2) = π²/6.
    Reached via the path:
    Binomial Theorem → geometric series → logarithm → dilogarithm → zeta function.
    This result is proved in Mathlib via Fourier analysis (Parseval's theorem). -/
theorem euler_basel :
    zetaFunction 2 = π ^ 2 / 6 := by
  simp only [zetaFunction]
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num]
  simp_rw [Real.rpow_natCast]
  simpa using ((hasSum_nat_add_iff' 1).mpr hasSum_zeta_two).tsum_eq
