import Mathlib
import HystericalResponse.Paper2.ResponseSector

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`, Section “Finite lifetime and the propagation length”.
-/

set_option autoImplicit false

namespace Paper2

noncomputable section

/-- Dimensionless finite-lifetime transition factor used in point-source estimates. -/
def finiteLifetimeTransition (r lam : ℝ) : ℝ :=
  lam * (1 - Real.exp (-r / lam)) / r^2

/--
TeX qualitative claim: λ = v/Γ sets the flat-regime scale.
Algebraic positivity is certified; radial asymptotics of the screened kernel remain
tagged when needed by later Galactic applications.
-/
theorem finite_lifetime_scale_pos (p : PositiveParams) :
    0 < propagationLength p :=
  propagationLength_pos p

end

end Paper2
