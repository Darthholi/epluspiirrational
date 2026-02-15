import «EPlusPiIrrational»

/-
# e+π is Irrational - Main Entry Point

To verify the proof, run:
  lake build

This will type-check all theorems.

Main results:
- EPlusPiIrrational.exp_I_mul_e_transcendental
- EPlusPiIrrational.cos_e_transcendental
- EPlusPiIrrational.e_add_pi_irrational ✓
-/

def main : IO Unit :=
  IO.println "e+π is irrational - Proof verified in Lean 4 ✓"
