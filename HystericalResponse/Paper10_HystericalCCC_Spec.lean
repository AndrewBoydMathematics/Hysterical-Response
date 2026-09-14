/-
TeX: `10_cyclic_cosmology/paper_10_hysterical_ccc.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Linear infrared electromagnetic instability     → Paper10.LinearEMSpectrum
   (Jacobian det → char poly; IR-first; band + IVT positive root)
2. Near-threshold growth                          → Paper10.NearThresholdGrowth
   (frozen-denominator algebraic onset; disclosed as such)
3. Reciprocal conformal matching                  → Paper10.ReciprocalMatching
   (C₀ and unit hot/cold; radiation identity; exact leading reciprocity)
4. Active versus passive CCC                      → Paper10.ActiveCrossover

No `sorry`. Nonlinear scalar–Maxwell pump remains a modelling assumption.
Four-dimensional Maxwell conformal invariance remains a literature hypothesis (Wald).
Little-o remainder in the outgoing de~Sitter asymptotic is disclosed, not claimed.
-/

import HystericalResponse.Paper10.LinearEMSpectrum
import HystericalResponse.Paper10.NearThresholdGrowth
import HystericalResponse.Paper10.ReciprocalMatching
import HystericalResponse.Paper10.ActiveCrossover
