/-
Copyright (c) 2024 BIU Students. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Liberman, Nick Sokolovsky
-/
import Mathlib.Data.Nat.Choose.Sum

/-! # The Binomial Theorem

This file formalizes the classical Binomial Theorem for a commutative semiring.
The main theorem is proved directly by induction, following the usual mathematical proof:

* prove the base case `n = 0`;
* use Pascal's identity to split each coefficient in row `n + 1`;
* rearrange the two resulting finite sums;
* apply the induction hypothesis.

The file also proves two standard consequences:

* the sum of row `n` in Pascal's triangle is `2 ^ n`;
* the alternating sum of a positive row is zero.
-/

open Finset BigOperators

-- ─────────────────────────────────────────────
-- The Classical Binomial Theorem
-- ─────────────────────────────────────────────

/-- The Binomial Theorem: (x + y)^n = Σ C(n,k) · x^k · y^(n-k)
    for every natural number n. The proof is by induction and is valid in any
    commutative semiring, including the natural numbers, integers, reals, and polynomials. -/
theorem binomial_theorem {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ k ∈ range (n + 1), x ^ k * y ^ (n - k) * n.choose k := by
  -- The k-th summand in row n of Pascal's triangle.
  let term : ℕ → ℕ → R :=
    fun n k ↦ x ^ k * y ^ (n - k) * n.choose k
  change (x + y) ^ n = ∑ k ∈ range (n + 1), term n k
  -- The first summand is y^n, and the summand after the last one is zero.
  have first_term : ∀ n, term n 0 = y ^ n := fun n ↦ by
    simp [term]
  have after_last_term : ∀ n, term n n.succ = 0 := fun n ↦ by
    simp [term]
  -- Pascal's identity splits every middle term in row n+1 into two terms
  -- coming from row n.
  have pascal_step :
      ∀ n k, k ∈ range n.succ →
        term n.succ k.succ = x * term n k + y * term n k.succ := by
    intro n k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    dsimp only [term]
    rw [Nat.choose_succ_succ, Nat.cast_add, mul_add]
    congr 1
    · rw [pow_succ' x, Nat.succ_sub_succ]
      ac_rfl
    · by_cases h : k = n
      · subst k
        simp
      · rw [Nat.succ_sub (lt_of_le_of_ne hkn h)]
        rw [pow_succ' y]
        ac_rfl
  induction n with
  | zero =>
      -- (x+y)^0 = 1, and row zero contains only C(0,0) = 1.
      simp [term]
  | succ n ih =>
      -- Multiply row n by (x+y), split it into an x-part and a y-part,
      -- shift the x-part by one place, and combine using Pascal's identity.
      rw [sum_range_succ', first_term,
        sum_congr rfl (pascal_step n), sum_add_distrib, add_assoc,
        pow_succ' (x + y), ih, add_mul, mul_sum, mul_sum]
      congr 1
      rw [sum_range_succ', sum_range_succ, first_term, after_last_term,
        mul_zero, add_zero, pow_succ']

/-- The sum of the binomial coefficients in row n is 2^n.
    Combinatorially, both sides count the subsets of an n-element set. -/
theorem sum_binomial_coeffs (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-- For a positive row, the alternating sum of the binomial coefficients is zero.
    Equivalently, the sums of the even- and odd-indexed coefficients are equal. -/
theorem alternating_sum_binomial (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range (n + 1), ((-1) ^ k * n.choose k : ℤ)) = 0 :=
  Int.alternating_sum_range_choose_of_ne hn.ne'
