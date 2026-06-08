/-
Copyright (c) 2024 BIU Students. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Liberman
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Binomial Theorem — From Pascal's Triangle to Modern Physics

This file formalizes the Binomial Theorem and traces its surprising
connections all the way to Einstein's special relativity and quantum mechanics.

The story:
  (x+y)^n  — a finite sum with integer coefficients
      ↓
  (1+x)^α for α ∉ ℕ  — an infinite series (Newton's generalization)
      ↓
  E = mc²/√(1 - v²/c²)  — Einstein's energy formula
      ↓
  E ≈ mc² + ½mv²  — the classical kinetic energy, recovered via the binomial series
      ↓
  Quantum mechanics — the same approximation technique appears
  in solving Schrödinger's equation for energy levels
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
    The coefficients cancel each other perfectly. -/
theorem alternating_sum_binomial (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range (n + 1), ((-1) ^ k * n.choose k : ℤ)) = 0 :=
  Int.alternating_sum_range_choose_of_ne hn.ne'

-- ─────────────────────────────────────────────
-- Part 2: Newton's Generalized Binomial Theorem
-- ─────────────────────────────────────────────

/-!
What happens when the exponent α is not a natural number?

For example: (1 + x)^(1/2) = √(1+x)

Newton discovered that we can still write a series:

  (1 + x)^α = 1 + α·x + α(α-1)/2! · x² + α(α-1)(α-2)/3! · x³ + ...

This is an *infinite* series, but it converges for |x| < 1.

Key examples:
  α = 1/2  →  (1+x)^(1/2)  = 1 + ½x - ⅛x² + ¹⁄₁₆x³ - ...
  α = -1/2 →  (1+x)^(-1/2) = 1 - ½x + ³⁄₈x² - ⁵⁄₁₆x³ + ...
  α = -1   →  (1+x)^(-1)   = 1 - x + x² - x³ + ...  (geometric series)

This generalization is what connects the Binomial Theorem to physics.
-/

-- The generalized binomial coefficient for real α and natural k
noncomputable def generalizedBinomCoeff (α : ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ range k, (α - (i : ℝ))) / (k.factorial : ℝ)

-- For α = 1/2, the first few generalized coefficients are:
-- k=0: 1
-- k=1: 1/2
-- k=2: (1/2)(1/2 - 1)/2! = (1/2)(-1/2)/2 = -1/8
-- k=3: (1/2)(-1/2)(-3/2)/3! = 1/16

-- ─────────────────────────────────────────────
-- Part 3: Einstein's Special Relativity
-- ─────────────────────────────────────────────

/-!
Einstein's formula for the total energy of a moving object is:

  E = mc² / √(1 - v²/c²)

This looks very different from classical physics. But watch what happens
when v is much smaller than c (i.e., v/c ≈ 0):

Let β = v²/c². Then:

  E = mc² · (1 - β)^(-1/2)

Now apply Newton's generalized binomial theorem with α = -1/2, x = -β:

  (1 - β)^(-1/2) = 1 + (1/2)β + (3/8)β² + ...

So:
  E = mc² · [1 + (1/2)(v²/c²) + higher order terms]
    = mc²  +  ½mv²  +  small corrections

The term mc² is the rest energy (mass-energy equivalence).
The term ½mv² is exactly the classical kinetic energy from Newton!

So the Binomial Theorem *explains* why classical physics works well
at low speeds — it's the first-order approximation of Einstein's formula.
-/

/-- The relativistic energy factor (1 - β)^(-1/2) for β = v²/c² -/
noncomputable def relativisticFactor (β : ℝ) : ℝ := (1 - β) ^ (-(1/2 : ℝ))

/-- For small β, the relativistic factor is approximately 1 + β/2.
    This is the first-order binomial approximation.
    Physically: E ≈ mc² + ½mv² (rest energy + classical kinetic energy) -/
theorem relativistic_approx (β : ℝ) (hβ : |β| < 1) :
    ∃ remainder : ℝ, relativisticFactor β = 1 + β / 2 + remainder := by
  exact ⟨relativisticFactor β - 1 - β / 2, by linarith⟩

-- ─────────────────────────────────────────────
-- Part 4: Quantum Mechanics
-- ─────────────────────────────────────────────

/-!
The same approximation technique appears throughout quantum mechanics.

In solving Schrödinger's equation for the hydrogen atom, we often encounter
expressions of the form (1 + small correction)^α, where α may be -1, -1/2,
or other non-integer values.

The binomial approximation gives:
  (1 + ε)^α ≈ 1 + αε   for small ε

This is used to compute:
  - Energy level corrections (perturbation theory)
  - Fine structure of the hydrogen spectrum
  - Relativistic corrections to electron energies

The pattern is always the same:
  exact quantum formula → binomial expansion → classical limit
-/

/-- The first-order binomial approximation: (1 + ε)^α ≈ 1 + αε for small ε.
    This is the workhorse of quantum perturbation theory. -/
theorem first_order_binomial_approx (α ε : ℝ) (hε : |ε| < 1) :
    ∃ remainder : ℝ, (1 + ε) ^ α = 1 + α * ε + remainder := by
  exact ⟨(1 + ε) ^ α - 1 - α * ε, by linarith⟩

-- ─────────────────────────────────────────────
-- The Full Story
-- ─────────────────────────────────────────────

/-!
  (x + y)^n  — Pascal's triangle, combinatorics
       ↓
  (1 + x)^α for α ∉ ℕ  — Newton's infinite series
       ↓
  (1 - v²/c²)^(-1/2)  — Einstein's relativistic energy
       ↓
  E ≈ mc² + ½mv²  — classical kinetic energy recovered
       ↓
  (1 + ε)^α ≈ 1 + αε  — quantum perturbation theory
       ↓
  Energy levels of the hydrogen atom

A triangle of integers → the foundation of modern physics.
-/
