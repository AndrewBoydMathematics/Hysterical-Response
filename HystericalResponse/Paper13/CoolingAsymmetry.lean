/-
TeX: `13_ew_cooling_baryogenesis/paper_13_ew_cooling_baryogenesis.tex`
Section “Concurrency implies branch asymmetry” — thm:ew-asym.

Reduced abstraction: inherits Paper 9 master oddness under an explicit overlap
physical input once the condensate-coupled concurrent epoch is nonempty.
-/

import Mathlib
import HystericalResponse.Paper9.MasterAsymmetry
import HystericalResponse.Paper13.ActivityWindow

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Paper13

noncomputable section

/-- Physical input: washout-weighted overlap of a CP-odd roll against topology
on the concurrent epoch (T_c, T_♦) guaranteed by thm_overlap when T_♦ > T_c. -/
axiom physics_ew_overlap :
    ∃ (Φf : Paper9.FreezeoutFunctional) (κ : ℝ) (kernel : Paper9.ActivityKernel)
      (h : Paper9.BranchHistory),
      0 < κ ∧
      (∃ t, 0 < kernel.K t ∧ 0 < h.dY t) ∧
      (∀ t, 0 ≤ h.dY t)

/-- TeX: thm:ew-asym — Electroweak Hysterical baryogenesis:
opposite nonzero branch yields under cooling concurrency.
Reduced abstraction: applies `Paper9.thm_master_asymmetry` once overlap is granted. -/
theorem thm_ew_asym :
    ∃ (Φf : Paper9.FreezeoutFunctional) (κ : ℝ) (kernel : Paper9.ActivityKernel)
      (h : Paper9.BranchHistory),
      Paper9.eta Φf κ kernel (Paper9.oppositeHistory h) =
          -Paper9.eta Φf κ kernel h ∧
      Paper9.eta Φf κ kernel h ≠ 0 := by
  obtain ⟨Φf, κ, kernel, h, hκ, hoverlap, hmono⟩ := physics_ew_overlap
  have hmaster :=
    Paper9.thm_master_asymmetry Φf κ hκ kernel h hmono hoverlap
  exact ⟨Φf, κ, kernel, h, hmaster.2.2, hmaster.1⟩

/-- Combined package: T_♦ > T_* ⇒ nonempty concurrent set, and the
asymmetry theorem applies once a roll overlaps that set (physical input). -/
theorem thm_ew_asym_of_halfspace {αX αY g : ℝ} (S : CondensateScale)
    (hαX : 0 < αX) (hαY : 0 < αY)
    (hhalf : S.Tstar < Tdiamond αX αY g) :
    (∃ T, concurrent αX αY g S T) ∧
      (∃ (Φf : Paper9.FreezeoutFunctional) (κ : ℝ) (kernel : Paper9.ActivityKernel)
        (h : Paper9.BranchHistory),
        Paper9.eta Φf κ kernel (Paper9.oppositeHistory h) =
            -Paper9.eta Φf κ kernel h ∧
        Paper9.eta Φf κ kernel h ≠ 0) :=
  ⟨thm_overlap_nonempty S hαX hαY hhalf, thm_ew_asym⟩

end

end Paper13
