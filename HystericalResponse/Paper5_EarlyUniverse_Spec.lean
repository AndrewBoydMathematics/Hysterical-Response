/-
TeX: `5_early_galactic_formation/paper_5_early_universe.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Cosmological closure / frozen Jacobian → Paper5.CosmologicalJacobian
2. Dust enhancement + Jeans extension    → Paper5.DustAndJeans

The master neutrality–instability theorem and finite threshold-time corollary
are *inherited* from Paper 1 (`boyd2026response`); they are not re-ported here.
This umbrella only checks the cosmological specialization facts claimed in TeX.
-/

import HystericalResponse.Paper5.CosmologicalJacobian
import HystericalResponse.Paper5.DustAndJeans
