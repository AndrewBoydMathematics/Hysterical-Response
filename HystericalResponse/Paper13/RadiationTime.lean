/-
TeX: `13_ew_cooling_baryogenesis/paper_13_ew_cooling_baryogenesis.tex`
Section “Radiation-era time estimate” — ass:radiation, cor:tdiamond.

Literature hypotheses only: the numerical T(t) law and the
∼10^{-11} s EW-scale estimate are not mathematical theorems.
-/

import Mathlib

set_option autoImplicit false

namespace Paper13

noncomputable section

/-- Literature: radiation-era prefactor in
`t ≃ (2.42 / √g_*) (MeV/T)² s` (Kolb & Turner). -/
axiom literature_radiation_prefactor_seconds : ℝ

axiom literature_radiation_prefactor_pos :
    0 < literature_radiation_prefactor_seconds

/-- Schematic radiation-era map t(T) = C / T² for T > 0 (reduced abstraction of
the Kolb–Turner formula with frozen g_* absorbed into C). -/
def radiationTime (C T : ℝ) : ℝ := C / T ^ 2

theorem radiationTime_pos {C T : ℝ} (hC : 0 < C) (hT : 0 < T) :
    0 < radiationTime C T :=
  div_pos hC (pow_pos hT 2)

/-- Phenomenological corollary witness: positive finite crossing time at any
positive electroweak-scale temperature. Numerical ∼10^{-11} s uses lattice
GeV edges from DOnofrio2014 and is not certified here. -/
theorem cor_tdiamond_pos {Td : ℝ} (hTd : 0 < Td) :
    0 < radiationTime literature_radiation_prefactor_seconds Td :=
  radiationTime_pos literature_radiation_prefactor_pos hTd

/-- Literature GeV plug-in placeholders (TeX ass:lattice). Used only for
seconds-scale phenomenology, not for the analytic overlap theorem. -/
axiom literature_Tc_GeV : ℝ
axiom literature_Tstar_GeV : ℝ
axiom literature_lattice_ordered :
    0 < literature_Tstar_GeV ∧ literature_Tstar_GeV < literature_Tc_GeV

end

end Paper13
