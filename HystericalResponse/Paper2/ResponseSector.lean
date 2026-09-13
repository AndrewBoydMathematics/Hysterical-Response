import Mathlib

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`,
Section “Stationary Hysterical Response and its ballistic spatial model”.

No new force carrier: this module is phase-space bookkeeping for the residual
response whose production source \(S\) is the Paper~1 drive, represented here
as a ballistic Wigner density.
-/

set_option autoImplicit false

namespace Paper2

open MeasureTheory Set Filter Topology

noncomputable section

abbrev Vec3 : Type := Fin 3 → ℝ

structure PositiveParams where
  v : ℝ
  Γ : ℝ
  v_pos : 0 < v
  Γ_pos : 0 < Γ

/-- Propagation length λ = v/Γ. -/
def propagationLength (p : PositiveParams) : ℝ :=
  p.v / p.Γ

theorem propagationLength_pos (p : PositiveParams) : 0 < propagationLength p :=
  div_pos p.v_pos p.Γ_pos

/-- Total response-production rate. -/
def totalSource (J : Vec3 → ℝ) : ℝ :=
  ∫ y, J y

/-- Retarded stationary solution along a ballistic characteristic (TeX eq. retarded). -/
def retardedSolution
    (Γ : ℝ)
    (S : Vec3 → Vec3 → ℝ)
    (x vel : Vec3) : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    Real.exp ((-Γ) * t) * S (x - t • vel) vel

/-- Source pulled back along the characteristic through `x` with velocity `vel`. -/
def sourceAlong (S : Vec3 → Vec3 → ℝ) (x vel : Vec3) (t : ℝ) : ℝ :=
  S (x - t • vel) vel

@[simp] theorem sourceAlong_zero (S : Vec3 → Vec3 → ℝ) (x vel : Vec3) :
    sourceAlong S x vel 0 = S x vel := by
  simp [sourceAlong]

theorem retardedSolution_eq_integral_sourceAlong
    (Γ : ℝ) (S : Vec3 → Vec3 → ℝ) (x vel : Vec3) :
    retardedSolution Γ S x vel =
      ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * sourceAlong S x vel t :=
  rfl

/-! ## Characteristic calculus for the transport PDE -/

theorem hasDerivAt_exp_neg_mul (Γ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp ((-Γ) * s))
      (Real.exp ((-Γ) * t) * (-Γ)) t := by
  have hlin0 : HasDerivAt (fun s : ℝ => (-Γ) * s) ((-Γ) * 1) t :=
    (hasDerivAt_id (𝕜 := ℝ) t).const_mul (-Γ)
  have hlin : HasDerivAt (fun s : ℝ => (-Γ) * s) (-Γ) t := by
    convert hlin0 using 1; ring
  exact (Real.hasDerivAt_exp ((-Γ) * t)).comp t hlin

theorem tendsto_weighted_φ_at_zero
    (Γ : ℝ) (φ : ℝ → ℝ) (hφ0 : ContinuousWithinAt φ (Ici (0 : ℝ)) 0) :
    Tendsto (fun t : ℝ => Real.exp ((-Γ) * t) * φ t) (𝓝[>] (0 : ℝ)) (𝓝 (φ 0)) := by
  have h1 : Tendsto (fun t : ℝ => Real.exp ((-Γ) * t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have : ContinuousAt (fun t : ℝ => Real.exp ((-Γ) * t)) 0 := by fun_prop
    simpa [Real.exp_zero] using this.continuousWithinAt.tendsto
  have hφ : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 (φ 0)) :=
    hφ0.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  convert h1.mul hφ using 1
  simp

/--
Integration by parts on \((0,\infty)\):
\(\int_0^\infty e^{-\Gamma t}\varphi'(t)\,dt = -\varphi(0)+\Gamma\int_0^\infty e^{-\Gamma t}\varphi(t)\,dt\).
-/
theorem characteristic_ibp
    {Γ : ℝ} (_hΓ : 0 < Γ) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt φ (deriv φ t) t)
    (hφ0 : ContinuousWithinAt φ (Ici (0 : ℝ)) 0)
    (hintφ : IntegrableOn (fun t => Real.exp ((-Γ) * t) * φ t) (Ioi 0))
    (hintφ' : IntegrableOn (fun t => Real.exp ((-Γ) * t) * deriv φ t) (Ioi 0))
    (htop : Tendsto (fun t : ℝ => Real.exp ((-Γ) * t) * φ t) atTop (𝓝 0)) :
    ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * deriv φ t =
      - φ 0 + Γ * ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * φ t := by
  set u : ℝ → ℝ := fun t => Real.exp ((-Γ) * t)
  set u' : ℝ → ℝ := fun t => Real.exp ((-Γ) * t) * (-Γ)
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := fun t _ => by
    simpa [u, u'] using hasDerivAt_exp_neg_mul Γ t
  have hbot := tendsto_weighted_φ_at_zero Γ φ hφ0
  have heq_u' : ∀ t, u' t * φ t = (-Γ) * (u t * φ t) := by
    intro t; simp [u, u']; ring
  have hint_u'φ : IntegrableOn (fun t => u' t * φ t) (Ioi 0) := by
    have : (fun t => u' t * φ t) = fun t => (-Γ) * (Real.exp ((-Γ) * t) * φ t) := by
      funext t; simp [heq_u', u]
    rw [this]
    exact hintφ.const_mul (-Γ)
  have hint_u'φ_pi : IntegrableOn (u' * φ) (Ioi 0) := by
    simpa [Pi.mul_def] using hint_u'φ
  have hint_uφ' : IntegrableOn (u * deriv φ) (Ioi 0) := by
    simpa [u, Pi.mul_def] using hintφ'
  have hmain :=
    integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := φ 0) (b' := (0 : ℝ))
      hu hφ hint_uφ' hint_u'φ_pi hbot htop
  have hrewritten :
      ∫ t in Ioi (0 : ℝ), u t * deriv φ t =
        -φ 0 - ∫ t in Ioi (0 : ℝ), u' t * φ t := by
    simpa using hmain
  have hpull :
      ∫ t in Ioi (0 : ℝ), u' t * φ t =
        (-Γ) * ∫ t in Ioi (0 : ℝ), u t * φ t := by
    have h1 : (fun t => u' t * φ t) = fun t => (-Γ) * (u t * φ t) := by
      funext t; exact heq_u' t
    simp_rw [h1, integral_const_mul]
  calc
    ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * deriv φ t
        = ∫ t in Ioi (0 : ℝ), u t * deriv φ t := rfl
    _ = -φ 0 - ∫ t in Ioi (0 : ℝ), u' t * φ t := hrewritten
    _ = -φ 0 - (-Γ) * ∫ t in Ioi (0 : ℝ), u t * φ t := by rw [hpull]
    _ = -φ 0 + Γ * ∫ t in Ioi (0 : ℝ), u t * φ t := by ring
    _ = -φ 0 + Γ * ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * φ t := rfl

/--
Directional derivative of the retarded solution along `vel`, obtained by the
characteristic chain rule under the integral
(`vel · ∇_x f = ∫ e^{-Γt} (-∂_t S(x-tv,v)) dt`).
-/
def retardedDirDeriv
    (Γ : ℝ) (S : Vec3 → Vec3 → ℝ) (x vel : Vec3) : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    Real.exp ((-Γ) * t) * (- deriv (sourceAlong S x vel) t)

/--
TeX: eqs. transport + retarded.

Under the standing regularity on the characteristic pullback
`φ(t)=S(x-tv,v)` (C¹ on `(0,∞)`, continuous at `0`, integrable against
`e^{-Γt}` together with `φ'`, and vanishing at infinity with that weight),
the retarded solution satisfies the stationary transport equation in the
characteristic sense

  `vel · ∇ f = S - Γ f`,

where the left-hand side is `retardedDirDeriv`.
-/
theorem thm_retarded_solves_transport
    {Γ : ℝ} (hΓ : 0 < Γ)
    (S : Vec3 → Vec3 → ℝ) (x vel : Vec3)
    (hφ : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (sourceAlong S x vel) (deriv (sourceAlong S x vel) t) t)
    (hφ0 : ContinuousWithinAt (sourceAlong S x vel) (Ici (0 : ℝ)) 0)
    (hintφ :
      IntegrableOn (fun t => Real.exp ((-Γ) * t) * sourceAlong S x vel t) (Ioi 0))
    (hintφ' :
      IntegrableOn (fun t => Real.exp ((-Γ) * t) * deriv (sourceAlong S x vel) t) (Ioi 0))
    (htop :
      Tendsto (fun t : ℝ => Real.exp ((-Γ) * t) * sourceAlong S x vel t) atTop (𝓝 0)) :
    retardedDirDeriv Γ S x vel =
      S x vel - Γ * retardedSolution Γ S x vel := by
  set φ := sourceAlong S x vel
  have hibp := characteristic_ibp (Γ := Γ) hΓ φ hφ hφ0 hintφ hintφ' htop
  have hneg :
      ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * (- deriv φ t) =
        - ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * deriv φ t := by
    simp [integral_neg, mul_neg]
  calc
    retardedDirDeriv Γ S x vel
        = ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * (- deriv φ t) := by
            simp [retardedDirDeriv, φ]
    _ = - ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * deriv φ t := hneg
    _ = - (- φ 0 + Γ * ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * φ t) := by
        rw [hibp]
    _ = φ 0 - Γ * ∫ t in Ioi (0 : ℝ), Real.exp ((-Γ) * t) * φ t := by ring
    _ = S x vel - Γ * retardedSolution Γ S x vel := by
        simp [φ, retardedSolution_eq_integral_sourceAlong]

/-- Alias matching the older axiom name; now a proved theorem. -/
theorem math_retarded_solves_transport
    {Γ : ℝ} (hΓ : 0 < Γ)
    (S : Vec3 → Vec3 → ℝ) (x vel : Vec3)
    (hφ : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (sourceAlong S x vel) (deriv (sourceAlong S x vel) t) t)
    (hφ0 : ContinuousWithinAt (sourceAlong S x vel) (Ici (0 : ℝ)) 0)
    (hintφ :
      IntegrableOn (fun t => Real.exp ((-Γ) * t) * sourceAlong S x vel t) (Ioi 0))
    (hintφ' :
      IntegrableOn (fun t => Real.exp ((-Γ) * t) * deriv (sourceAlong S x vel) t) (Ioi 0))
    (htop :
      Tendsto (fun t : ℝ => Real.exp ((-Γ) * t) * sourceAlong S x vel t) atTop (𝓝 0)) :
    retardedDirDeriv Γ S x vel =
      S x vel - Γ * retardedSolution Γ S x vel :=
  thm_retarded_solves_transport hΓ S x vel hφ hφ0 hintφ hintφ' htop

end

end Paper2
