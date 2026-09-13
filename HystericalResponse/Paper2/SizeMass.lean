import Mathlib

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`, Section “Late-time size–mass scaling under isotropic accretion”.
-/

set_option autoImplicit false

namespace Paper2

noncomputable section

/--
PHYSICS: isotropic/spherical virial specific AM scales as j ∝ M^{2/3}
(TeX Assumption iso-accretion).
Physical justification in TeX: late-time feeding from a homogeneous
intergalactic dust/gas reservoir (no preferred inflow direction).
-/
axiom physics_isotropic_accretion_am : Prop

/--
PHYSICS: characteristic size proxy R ∼ j / v_f (TeX Assumption size-proxy).
-/
axiom physics_size_proxy_j_over_v : Prop

/--
Exponent identity used in the TeX proof sketch:
(2/3) − (1/4) = 5/12.
-/
theorem size_mass_exponent_identity :
    (2 : ℝ) / 3 - 1 / 4 = 5 / 12 := by
  norm_num

/--
Power subtraction used by the size–mass argument:
M^(2/3) / M^(1/4) = M^(5/12) for M > 0.
-/
theorem size_mass_rpow_sub
    (M : ℝ)
    (hM : 0 < M) :
    M ^ ((2 : ℝ) / 3) / M ^ ((1 : ℝ) / 4) = M ^ ((5 : ℝ) / 12) := by
  rw [← Real.rpow_sub hM]
  norm_num

/--
TeX: thm:size-mass — Late-time size–mass exponent (algebraic form).
If v_f = c_v · M^{1/4} and R = c · M^{2/3} / v_f with positive prefactors, then
R = (c / c_v) · M^{5/12}.
-/
theorem thm_size_mass_isotropic_accretion
    (M vf R c_v c : ℝ)
    (hM : 0 < M)
    (hcv : 0 < c_v)
    (hv : vf = c_v * M ^ ((1 : ℝ) / 4))
    (hR : R = c * M ^ ((2 : ℝ) / 3) / vf) :
    R = (c / c_v) * M ^ ((5 : ℝ) / 12) := by
  have hcv0 : c_v ≠ 0 := ne_of_gt hcv
  rw [hR, hv]
  -- c * M^(2/3) / (c_v * M^(1/4)) = (c/c_v) * (M^(2/3)/M^(1/4))
  have hsplit :
      c * M ^ ((2 : ℝ) / 3) / (c_v * M ^ ((1 : ℝ) / 4)) =
        (c / c_v) * (M ^ ((2 : ℝ) / 3) / M ^ ((1 : ℝ) / 4)) := by
    field_simp [hcv0]
  rw [hsplit, size_mass_rpow_sub M hM]

end

end Paper2
