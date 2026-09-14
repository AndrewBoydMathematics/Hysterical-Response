/-
TeX: `13_ew_cooling_baryogenesis/paper_13_ew_cooling_baryogenesis.tex`
Remark converse / open-g placement — dual of forced cooling criticality:
choose g so that criticality sits at a target temperature Td.
Ported from the retired electroweak baryon companion (Paper 7).
-/

import Mathlib
import HystericalResponse.Paper13.InheritedResidual

set_option autoImplicit false

namespace Paper13

noncomputable section

/-- Coupling that places Debye criticality at target temperature `Td`. -/
def gDiamond (αX αY Td : ℝ) : ℝ := Real.sqrt (αX * αY) * Td ^ 2

theorem gDiamond_sq {αX αY Td : ℝ} (hαX : 0 ≤ αX) (hαY : 0 ≤ αY) :
    gDiamond αX αY Td ^ 2 = αX * αY * Td ^ 4 := by
  unfold gDiamond
  have hsq : (Real.sqrt (αX * αY)) ^ 2 = αX * αY :=
    Real.sq_sqrt (mul_nonneg hαX hαY)
  calc
    (Real.sqrt (αX * αY) * Td ^ 2) ^ 2
        = (Real.sqrt (αX * αY)) ^ 2 * (Td ^ 2) ^ 2 := by ring
    _ = αX * αY * Td ^ 4 := by rw [hsq]; ring

theorem Delta_gDiamond {αX αY Td T : ℝ}
    (hαX : 0 ≤ αX) (hαY : 0 ≤ αY) :
    Delta αX αY (gDiamond αX αY Td) T = αX * αY * (T ^ 4 - Td ^ 4) := by
  rw [Delta_eq, gDiamond_sq hαX hαY]
  ring

/-- Criticality at the chosen target temperature. -/
theorem thm_ew_window_critical {αX αY Td : ℝ}
    (hαX : 0 ≤ αX) (hαY : 0 ≤ αY) :
    Delta αX αY (gDiamond αX αY Td) Td = 0 := by
  rw [Delta_gDiamond hαX hαY]; ring

/-- TeX: rem:converse / thm:ew-window — place criticality in (T_*, T_c) by choosing g. -/
theorem thm_ew_window {αX αY Tstar Tc Td : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY)
    (hlo : Tstar < Td) (hhi : Td < Tc) :
    Tstar < Td ∧ Td < Tc ∧
      Delta αX αY (gDiamond αX αY Td) Td = 0 :=
  ⟨hlo, hhi, thm_ew_window_critical hαX.le hαY.le⟩

theorem thm_ew_window_supercritical_pow {αX αY Td T : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY) (hp : T ^ 4 < Td ^ 4) :
    Delta αX αY (gDiamond αX αY Td) T < 0 := by
  rw [Delta_gDiamond hαX.le hαY.le]
  exact mul_neg_of_pos_of_neg (mul_pos hαX hαY) (sub_neg.mpr hp)

theorem thm_ew_window_subcritical_pow {αX αY Td T : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY) (hp : Td ^ 4 < T ^ 4) :
    0 < Delta αX αY (gDiamond αX αY Td) T := by
  rw [Delta_gDiamond hαX.le hαY.le]
  exact mul_pos (mul_pos hαX hαY) (sub_pos.mpr hp)

end

end Paper13
