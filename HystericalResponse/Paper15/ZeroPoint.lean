import Mathlib
import HystericalResponse.Paper15.MemoryScale

/-
TeX: `15_btfr_zero_point/paper_15_btfr_zero_point.tex`,
Section “Zero-point matching and main theorem”.
-/

set_option autoImplicit false

namespace Paper15

noncomputable section

/-- TeX: ass:attractor — mature BTFR attractor normalization. -/
axiom physics_mature_attractor : True

/-- TeX: ass:halo-IR — far-halo residual IR-pinned to cosmological horizon memory. -/
axiom physics_far_halo_IR_pin : True

/-- TeX: ass:zero-match — mature BTFR zero point equals a_IR. -/
axiom physics_zero_point_match : True

/--
TeX: thm:a0 — under a₀ = a_IR and thm:aIR, a₀ = H₀ c / 2π.
Reduced abstraction: algebraic consequence of matching + period identities;
physical assumptions and literature hypotheses are tagged axioms.
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
TeX: thm:a0 velocity form — v_f⁴ = G (H₀ c / 2π) M when K = G a₀.
-/
theorem thm_a0_velocity
    (H0 c G M vf K a0 : ℝ)
    (hK : K = G * a0)
    (ha0 : a0 = H0 * c / (2 * Real.pi))
    (hvf : vf ^ 4 = K * M) :
    vf ^ 4 = G * (H0 * c / (2 * Real.pi)) * M := by
  calc
    vf ^ 4 = K * M := hvf
    _ = (G * a0) * M := by rw [hK]
    _ = G * (H0 * c / (2 * Real.pi)) * M := by
      simp [ha0, mul_assoc]

end

end Paper15
