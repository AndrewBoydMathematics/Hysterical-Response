import Mathlib

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`,
Section “Cosmological IR floor and the BTFR zero point”.
-/

set_option autoImplicit false

namespace Paper2

noncomputable section

/-- TeX: lit:period — Euclidean/KMS period β = 2π/κ. -/
axiom literature_euclidean_horizon_period :
    True

/-- TeX: lit:cosmo-kappa — cosmological horizon κ = H₀. -/
axiom literature_cosmo_horizon_surface_gravity :
    True

/-- TeX: ass:halo-IR — far-halo residual IR-pinned to cosmological horizon memory. -/
axiom physics_far_halo_IR_pin :
    True

/-- TeX: ass:zero-match — mature BTFR zero point equals a_IR. -/
axiom physics_zero_point_match :
    True

/--
TeX: def:aIR / thm:aIR — a_IR = c/β with β = 2π/κ and κ = H₀ gives a_IR = H₀ c / 2π.
-/
theorem thm_aIR
    (H0 c β κ aIR : ℝ)
    (hβ : β = (2 * Real.pi) / κ)
    (hκ : κ = H0)
    (hpos : κ ≠ 0)
    (ha : aIR = c / β) :
    aIR = H0 * c / (2 * Real.pi) := by
  have hβ' : β = (2 * Real.pi) / H0 := by simp [hβ, hκ]
  have hH0 : H0 ≠ 0 := by simpa [hκ] using hpos
  calc
    aIR = c / β := ha
    _ = c / ((2 * Real.pi) / H0) := by rw [hβ']
    _ = c * (H0 / (2 * Real.pi)) := by field_simp [hH0]
    _ = H0 * c / (2 * Real.pi) := by ring

/--
TeX: thm:a0 — under a₀ = a_IR and thm:aIR, a₀ = H₀ c / 2π.
Reduced abstraction: algebraic consequence of the matching and period identities;
Assumptions ass:halo-IR / ass:zero-match and literature hypotheses are tagged axioms above.
-/
theorem thm_a0
    (H0 c β κ aIR a0 : ℝ)
    (hβ : β = (2 * Real.pi) / κ)
    (hκ : κ = H0)
    (hpos : κ ≠ 0)
    (ha : aIR = c / β)
    (hmatch : a0 = aIR) :
    a0 = H0 * c / (2 * Real.pi) := by
  rw [hmatch]
  exact thm_aIR H0 c β κ aIR hβ hκ hpos ha

/--
TeX: thm:a0 velocity form — v_f⁴ = G (H₀ c / 2π) M on the attractor when K = G a₀.
-/
theorem thm_a0_velocity
    (H0 c G M vf K a0 : ℝ)
    (hK : K = G * a0)
    (ha0 : a0 = H0 * c / (2 * Real.pi))
    (hvf : vf^4 = K * M) :
    vf^4 = G * (H0 * c / (2 * Real.pi)) * M := by
  calc
    vf^4 = K * M := hvf
    _ = (G * a0) * M := by rw [hK]
    _ = G * (H0 * c / (2 * Real.pi)) * M := by
      simp [ha0, mul_assoc]

end

end Paper2
