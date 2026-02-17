/-
Copyright (c) 2026 Martin et al. All rights reserved.

# Basic Definitions for e+π Irrationality Proof

This file sets up the basic definitions and axioms needed for proving e+π is irrational.

## Main Definitions

- `e`: The number exp(1) (Euler's number)
- `α`: The number exp(I*e)
- `Transcendental`: A number is transcendental if it's not algebraic

## Axioms (Standard Results)

- `e_transcendental`: e is transcendental (Hermite 1873)
- `transcendental_powers_linearIndependent`: Powers of transcendentals are independent
  (follows from Lindemann-Weierstrass)

-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational

noncomputable section

namespace EPlusPiIrrational

open Complex Real BigOperators

/-! ## Basic Definitions -/

/-- Euler's number: e = exp(1) -/
def e : ℂ := Complex.exp 1

/-- The key constant: α = exp(I*e) -/
def α : ℂ := Complex.exp (I * e)

/-- A complex number is transcendental if it is not algebraic over ℚ -/
def Transcendental (z : ℂ) : Prop := ¬ IsAlgebraic ℚ z

/-! ## Axioms for Standard Results -/

/-- Hermite's Theorem (1873): e is transcendental

This is one of the fundamental results in transcendental number theory.
The proof uses Padé approximation and auxiliary functions.

Reference: Hermite, C. (1873). "Sur la fonction exponentielle".
Comptes Rendus de l'Académie des Sciences, 77, 18-24.
-/
axiom e_transcendental : Transcendental e

/-- Linear Independence of Powers of Transcendental Numbers

If β is transcendental over ℚ, then any finite collection of its powers
{1, β, β², ..., β^n} are linearly independent over ℚ.

This follows from the Lindemann-Weierstrass theorem.

Reference: Baker, A. (1975). Transcendental Number Theory, Chapter 1.
-/
axiom transcendental_powers_linearIndependent (β : ℂ)
    (htrans : Transcendental β) (n : ℕ) :
    LinearIndependent ℚ (fun j : Fin n => β ^ (j : ℕ))

/-! ## Basic Properties -/

/-- e as a real number (for the final theorem statement) -/
def e_real : ℝ := Real.exp 1

lemma e_eq_exp_one : (e_real : ℂ) = e := by
  unfold e_real e
  simp [Complex.ofReal_exp]

end EPlusPiIrrational

end
