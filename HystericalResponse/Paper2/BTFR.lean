import Mathlib
import HystericalResponse.Paper2.ResponseClosure
import HystericalResponse.Paper2.CapacityAssembly

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`, Section “Analytic baryonic Tully–Fisher scaling”.
-/

set_option autoImplicit false

namespace Paper2

noncomputable section

/--
TeX: cor:btfr — if v_f² = C Q and Q² = (A²/y*) M then v_f⁴ = (C² A² / y*) M.
-/
theorem cor_btfr
    (C A M Q vf ystar : ℝ)
    (hy : ystar ≠ 0)
    (hv : vf^2 = C * Q)
    (hQM : Q^2 = (A^2 / ystar) * M) :
    vf^4 = (C^2 * A^2 / ystar) * M := by
  calc
    vf^4 = (vf^2)^2 := by ring
    _ = (C * Q)^2 := by rw [hv]
    _ = C^2 * Q^2 := by ring
    _ = C^2 * ((A^2 / ystar) * M) := by rw [hQM]
    _ = (C^2 * A^2 / ystar) * M := by
      field_simp [hy]

theorem btfr_from_response_attractor
    (C A M Q vf ystar : ℝ)
    (hy : ystar ≠ 0)
    (hv : vf^2 = C * Q)
    (hQM : Q^2 = (A^2 / ystar) * M) :
    vf^4 = (C^2 * A^2 / ystar) * M :=
  cor_btfr C A M Q vf ystar hy hv hQM

theorem btfr_quasistationary
    (C A M Q vf : ℝ)
    (hv : vf^2 = C * Q)
    (hQM : Q^2 = A^2 * M) :
    vf^4 = C^2 * A^2 * M := by
  calc
    vf^4 = (vf^2)^2 := by ring
    _ = (C * Q)^2 := by rw [hv]
    _ = C^2 * Q^2 := by ring
    _ = C^2 * (A^2 * M) := by rw [hQM]
    _ = C^2 * A^2 * M := by ring

end

end Paper2
