/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Ballistic response sector   → Paper2.ResponseSector
2. Ballistic halo              → Paper2.BallisticHalo
3. Finite lifetime             → Paper2.FiniteLifetime
4. Response closures / flat RC → Paper2.ResponseClosure
5. Capacity + assembly         → Paper2.CapacityAssembly
6. BTFR scaling                → Paper2.BTFR
7. Size–mass (isotropic accr.) → Paper2.SizeMass
8. Oblate geometry             → Paper2.OblateGeometry

Named theorems use TeX labels (`thm_…`, `cor_…`) where ported.
See `.cursor/rules/lean-tex-alignment.mdc` and `paper-series-standard.mdc`.
-/

import HystericalResponse.Paper2.ResponseSector
import HystericalResponse.Paper2.BallisticHalo
import HystericalResponse.Paper2.FiniteLifetime
import HystericalResponse.Paper2.ResponseClosure
import HystericalResponse.Paper2.CapacityAssembly
import HystericalResponse.Paper2.BTFR
import HystericalResponse.Paper2.SizeMass
import HystericalResponse.Paper2.OblateGeometry
