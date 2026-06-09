/-
Copyright (c) 2024 BIU Students. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Liberman, Nick Sokolovsky
-/
import Mathlib

/-! # Elementary Gauss Sum Proofs

Basic Lean exercises culminating in the formula for the sum of the first `n` natural numbers.
-/

open Finset

-- Exercise 1
example : 1 + 2 + 3 + 4 = 10 := by
  rfl

-- Exercise 2
example : ∀ n : ℕ, n + 0 = n := by
  intro n
  omega

example : ∀ a b : ℕ, a ≤ b → a + 1 ≤ b + 1 := by
  intro a b h
  omega

-- Exercise 3
example : ∑ i ∈ range 5, i = 10 := by
  decide

example : ∑ i ∈ range 11, i = 55 := by
  decide

-- Exercise 4
example (n : ℕ) : ∑ _i ∈ range (n + 1), 1 = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_range_succ, ih]

-- Exercise 5
example (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    ring
