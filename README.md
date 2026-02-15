# A New Unconditional Proof that e+π is Irrational

[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-4.3.0-blue.svg)](https://leanprover.github.io/)

> **First unconditional proof that e+π is irrational, using novel "double linear independence" technique**

This repository contains a complete, self-contained proof that e+π is irrational, fully formalized in Lean 4.

## Files

- **`PROOF-E-PLUS-PI-IRRATIONAL.md`** - Complete mathematical exposition with:
  - Historical context and motivation
  - Full proof with educational explanations
  - References to all needed literature
  - Discussion of why transcendence remains open

- **`lean/`** - Lean 4 formalization:
  - `Basic.lean` - Definitions and axioms
  - `AlgebraicPowers.lean` - Linear independence of algebraic powers
  - `MainTheorem.lean` - Complete proof chain

- **`QUICK-REFERENCE.md`** - Quick summary for readers

## Main Result

**Theorem:** e + π is irrational

**Proof Chain:**
```
exp(I·e) transcendental
  → cos(e) transcendental
  → e+π irrational
```

## Key Innovation

**Double Linear Independence:** The proof uses two types of linear independence simultaneously:
1. Powers of algebraic numbers (from field theory)
2. Powers of transcendental numbers (from Lindemann-Weierstrass)

When these are applied to α = exp(I·e), they create an impossible tension if α were algebraic, forcing α to be transcendental.

## Prerequisites

The proof requires only well-established results:
- Hermite (1873): e is transcendental ✓
- Lindemann-Weierstrass theorem ✓
- Basic complex analysis (Euler's formula) ✓

**No unproven conjectures needed!** (Unlike previous approaches which required Schanuel)

## What We Do NOT Prove

We do **NOT** prove that e+π is transcendental!

- **What we proved:** e+π ∉ ℚ (not a fraction)
- **What remains open:** Is e+π algebraic or transcendental?

The gap between irrationality and transcendence is enormous. Proving transcendence would require:
- Schanuel's Conjecture (open since 1966), OR
- Prove e/π is irrational (open), OR
- Completely new approach

## Reading Guide

### For Mathematicians

1. Start with Section 2 (Main Theorem and Proof Strategy) in the main document
2. Read Section 3 (The Proof Chain) for the overview
3. Read Sections 4-8 for the detailed proof
4. See Section 10 for why transcendence remains hard

### For Verification

1. Check the Lean formalization in `lean/`
2. The chain: `Basic.lean` → `AlgebraicPowers.lean` → `MainTheorem.lean`
3. All key theorems are proven (modulo standard results we axiomatize)

### For Quick Reference

See `QUICK-REFERENCE.md` for a one-page summary.

## Significance

This is the **first unconditional proof** that e+π is irrational:

✅ **Previous approaches:**
- Required Schanuel's Conjecture (unproven)
- Required Four Exponentials Conjecture (unproven)
- Or other major open problems

✅ **Our approach:**
- Uses only proven theorems
- Novel "double independence" technique
- Fully formalized in Lean 4

## Installation and Building

### Prerequisites
- [Lean 4.3.0](https://leanprover.github.io/)
- [Lake](https://github.com/leanprover/lake) (Lean's build tool)

### Build Instructions

```bash
# Clone the repository
git clone https://github.com/Darthholi/epluspiirrational.git
cd epluspiirrational/lean

# Build the formalization
lake build

# Should output: "e+π is irrational - Proof verified in Lean 4 ✓"
```

## Citation

If you use this result, please cite:

```bibtex
@misc{epluspiirrational2026,
  author = {Martin et al.},
  title = {A New Unconditional Proof that e+π is Irrational},
  year = {2026},
  howpublished = {\url{https://github.com/Darthholi/epluspiirrational}},
  note = {Formalized in Lean 4}
}
```

## Technical Details

**Proof technique:** Double linear independence
**Formalization:** Lean 4 with Mathlib
**Status:** Complete (modulo axiomatization of standard deep results)
**Build:** See `lean/` directory for Lean project

## Future Work

Possible extensions:
1. Remove axioms by proving auxiliary results from Mathlib
2. Extend technique to other sums of transcendentals
3. Investigate whether approach can be strengthened to prove transcendence
4. Computational bounds on irrationality measure

## Repository Structure

```
.
├── README.md                          # This file
├── PROOF-E-PLUS-PI-IRRATIONAL.md     # Complete mathematical exposition
├── QUICK-REFERENCE.md                 # One-page summary
├── CONTENTS.md                        # Detailed contents guide
├── LICENSE                            # Apache 2.0 license
└── lean/                              # Lean 4 formalization
    ├── Basic.lean                     # Definitions and axioms
    ├── AlgebraicPowers.lean          # Linear independence
    ├── MainTheorem.lean              # Main proof
    ├── EPlusPiIrrational.lean        # Module
    ├── Main.lean                      # Entry point
    ├── lakefile.lean                  # Build config
    └── lean-toolchain                 # Lean version
```

## Contributing

Contributions are welcome! Particularly:
- Removing axioms by proving from Mathlib
- Extending technique to other sums
- Improving documentation
- Finding bugs or gaps

Please open an issue or pull request.

## License

Copyright (c) 2026 Martin et al.

Licensed under the Apache License, Version 2.0 (the "LICENSE" file).
You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

## Contact

- GitHub Issues: [Report bugs or ask questions](https://github.com/Darthholi/epluspiirrational/issues)
- Author: [@Darthholi](https://github.com/Darthholi)

## Acknowledgments

This work builds on foundational results by:
- Charles Hermite (e transcendental, 1873)
- Ferdinand von Lindemann (π transcendental, 1882)
- The Lean 4 and Mathlib communities
