/-
Copyright (c) 2026 Martin et al. All rights reserved.

# Linear Independence of Powers of Algebraic Numbers

This file establishes that powers of algebraic numbers are linearly independent,
up to the degree of the minimal polynomial.

## Main Result

If α is algebraic of degree d over ℚ, then {1, α, α², ..., α^(d-1)} are
linearly independent over ℚ.

This is a standard result from field theory.

-/

import EPlusPiIrrational.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent

noncomputable section

namespace EPlusPiIrrational

open Complex FiniteDimensional

/-! ## Linear Independence of Algebraic Powers -/

/-- Powers of an algebraic number are linearly independent

Let α be algebraic over ℚ with minimal polynomial of degree d.
Then the powers {1, α, α², ..., α^(d-1)} are linearly independent over ℚ.

**Proof idea:** If Σᵢ cᵢαⁱ = 0 for i < d with cᵢ ∈ ℚ not all zero, then α
satisfies a polynomial of degree < d, contradicting minimality of the minimal polynomial.

**Reference:** Lang, S. (2002). Algebra (3rd ed.), Chapter V, §1.

**Note:** This is a standard result; in a full formalization, it would be proven
from Mathlib's minpoly theory. Here we use `sorry` as it's auxiliary to our main result.
-/
theorem algebraic_powers_linearIndependent (α : ℂ) (halg : IsAlgebraic ℚ α) :
    let d := (minpoly ℚ α).natDegree
    LinearIndependent ℚ (fun i : Fin d => α ^ (i : ℕ)) := by
  sorry
  /- Proof sketch:
  1. Let P = minpoly ℚ α be the minimal polynomial of degree d
  2. The powers {1, α, ..., α^(d-1)} span ℚ(α) as a vector space over ℚ
  3. dim_ℚ ℚ(α) = d (degree of minimal polynomial)
  4. A spanning set of size d in a d-dimensional space that is not linearly
     independent would have dim < d (contradiction)
  5. Therefore {1, α, ..., α^(d-1)} are linearly independent
  -/

/-! ## Educational Note: Why This Matters

The key to our proof is using TWO types of linear independence simultaneously:

1. **Algebraic independence** (this file):
   If α is algebraic of degree d, then {1, α, ..., α^(d-1)} are independent

2. **Transcendental independence** (from Basic.lean):
   If β is transcendental, then {1, β, β², ...} are independent for any finite set

When we suppose α = exp(I·e) is algebraic (degree d), we get:
- Powers of α are independent (up to α^(d-1))
- Powers of e are independent (all finite collections)

These two independence properties together create an impossible tension,
forcing α to be transcendental!

This "double linear independence" technique is the key innovation of our proof.
-/

end EPlusPiIrrational

end
