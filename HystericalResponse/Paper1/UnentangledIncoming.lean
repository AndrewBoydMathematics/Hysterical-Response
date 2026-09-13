import Mathlib

/-!
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Sections: **Unentangled incoming particles and the driven response equation**
and **Finite-dimensional Everett toy: large-n off-diagonal feed**.

Algebraic core of:
* `thm:driven-deviation` — \(\dot{\delta\rho}=\mathcal L\delta\rho+\mathcal S\)
* `thm:offdiag-source` — diagonal-preserving arrival ⇒ \(\Delta\mathcal S=0\)
* `prop:S-Jin` — source scales with arrival rate / \(J_{\mathrm{in}}\)

Reduced abstraction: linear maps on a real module (no CPTP/Hilbert data).
Physical: `physics_large_n_diagonal_protection`, `physics_jout_sets_decoherence_scale`.
Literature (TeX remarks): Joos–Zeh / Hornberger–Sipe flux decoherence; Gardiner–Zoller / Breuer–Petruccione driven form.
-/

set_option autoImplicit false

namespace Paper1.UnentangledIncoming

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- Arrival generator piece `ν (E - id)`. -/
def arrivalGenerator (E : X →ₗ[ℝ] X) (ν : ℝ) : X →ₗ[ℝ] X :=
  ν • (E - LinearMap.id)

/-- Full linearized generator `L_D + ν (E - id)`. -/
def fullGenerator (L_D E : X →ₗ[ℝ] X) (ν : ℝ) : X →ₗ[ℝ] X :=
  L_D + arrivalGenerator E ν

/-- Residual source `S = ν (E ρ₀ - ρ₀)`. -/
def residualSource (E : X →ₗ[ℝ] X) (ν : ℝ) (ρ0 : X) : X :=
  ν • (E ρ0 - ρ0)

/--
TeX: thm:driven-deviation — substitute `ρ = ρ₀ + δ` into
`ρ̇ = L_D ρ + ν (E ρ - ρ)` with `L_D ρ₀ = 0`.
-/
theorem thm_driven_deviation
    (L_D E : X →ₗ[ℝ] X) (ν : ℝ) (ρ0 δ : X)
    (hfix : L_D ρ0 = 0) :
    L_D (ρ0 + δ) + ν • (E (ρ0 + δ) - (ρ0 + δ)) =
      fullGenerator L_D E ν δ + residualSource E ν ρ0 := by
  -- Expand both sides with linearity of `L_D` and `E`.
  have lhs :
      L_D (ρ0 + δ) + ν • (E (ρ0 + δ) - (ρ0 + δ)) =
        L_D δ + ν • (E δ - δ) + ν • (E ρ0 - ρ0) := by
    calc
      L_D (ρ0 + δ) + ν • (E (ρ0 + δ) - (ρ0 + δ))
          = L_D ρ0 + L_D δ + ν • (E ρ0 + E δ - ρ0 - δ) := by
              simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = L_D δ + ν • (E ρ0 + E δ - ρ0 - δ) := by simp [hfix]
      _ = L_D δ + ν • ((E δ - δ) + (E ρ0 - ρ0)) := by
              congr 1
              abel_nf
      _ = L_D δ + ν • (E δ - δ) + ν • (E ρ0 - ρ0) := by
              simp [smul_add, add_assoc]
  have rhs :
      fullGenerator L_D E ν δ + residualSource E ν ρ0 =
        L_D δ + ν • (E δ - δ) + ν • (E ρ0 - ρ0) := by
    simp [fullGenerator, arrivalGenerator, residualSource, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
      smul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  exact lhs.trans rhs.symm

/--
TeX: thm:offdiag-source — if incorporation preserves the classicalization of `ρ₀`,
then `Δ S = 0` (purely off-classical residual drive).
-/
theorem thm_offdiag_source
    (Δ E : X →ₗ[ℝ] X) (ν : ℝ) (ρ0 : X)
    (hpres : Δ (E ρ0) = Δ ρ0) :
    Δ (residualSource E ν ρ0) = 0 := by
  have h : Δ (E ρ0 - ρ0) = 0 := by
    simp [map_sub, hpres, sub_self]
  simp [residualSource, map_smul, h, smul_zero]

/--
PHYSICS: large-`n` Everett pointer modelling hypothesis
(TeX Assumption large-n-diag): unentangled incoming incorporation does not
change the diagonal of the classical reference at leading order.
-/
axiom physics_large_n_diagonal_protection : Prop

/--
PHYSICS: outgoing / monitored exchange sets the decoherence rate scale
`γ ∼ J_out` (TeX Assumption Jout-decoherence; Joos–Zeh / Hornberger–Sipe
collisional flux scaling and loss-Lindblad emission rates in the literature).
-/
axiom physics_jout_sets_decoherence_scale : Prop

/--
TeX: prop:S-Jin — `‖residualSource E ν ρ0‖` scales with the arrival rate `ν`
at fixed per-particle kick (incoming flux dictionary).
-/
theorem prop_source_scales_with_arrival_rate
    (E : X →ₗ[ℝ] X) (ν : ℝ) (ρ0 : X) :
    residualSource E ν ρ0 = ν • (E ρ0 - ρ0) :=
  rfl

end

end Paper1.UnentangledIncoming
