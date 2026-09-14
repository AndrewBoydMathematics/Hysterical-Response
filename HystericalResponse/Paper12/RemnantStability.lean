import Mathlib
import HystericalResponse.Paper12.WakeDynamics

/-!
TeX: `12_nonsingular_gravitational_collapse/paper_12_nonsingular_collapse.tex`,
Section “Linear stability and dissipative attraction”.

Certifies the TeX damped-attraction argument: every complex characteristic root has
negative real part, and the standard linear solution forms decay as `t → ∞`.
-/

set_option autoImplicit false

namespace Paper12

noncomputable section

open Filter Topology

/-- TeX differentiation of `F(R) = H(R) - GM/R²`: slope relation at a point. -/
def forceSlope (H' GM R : ℝ) : ℝ :=
  H' + 2 * GM / R ^ 3

/-- TeX: lem:slope — H'(R_*) < −2 GM/R_*^3 ⇒ F'(R_*) < 0. -/
theorem lem_slope {H' GM Rstar : ℝ}
    (hstr : H' < - (2 * GM / Rstar ^ 3)) :
    forceSlope H' GM Rstar < 0 := by
  unfold forceSlope
  linarith

/-- Real characteristic polynomial of the linearised damped remnant ODE. -/
def charPoly (gamma kappa s : ℝ) : ℝ :=
  s ^ 2 + gamma * s + kappa

/-- Complex characteristic polynomial (TeX eq:char). -/
def charPolyℂ (gamma kappa : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 + (gamma : ℂ) * z + (kappa : ℂ)

/-- TeX packaging of a restoring, damped remnant equilibrium. -/
structure RestoringRemnant where
  Rstar : ℝ
  Fprime : ℝ
  gamma : ℝ
  hR : 0 < Rstar
  hRest : Fprime < 0
  hDamp : 0 < gamma

/-- Stiffness κ = −F' > 0. -/
def RestoringRemnant.kappa (S : RestoringRemnant) : ℝ := -S.Fprime

theorem RestoringRemnant.kappa_pos (S : RestoringRemnant) : 0 < S.kappa :=
  neg_pos.mpr S.hRest

/-- TeX: prop:undamped — s² = F' has no real solution when F' < 0. -/
theorem prop_undamped {Fprime : ℝ} (hF : Fprime < 0) :
    ¬ ∃ s : ℝ, s ^ 2 = Fprime := by
  rintro ⟨s, hs⟩
  have : 0 ≤ s ^ 2 := sq_nonneg s
  linarith

/-- Real roots of s² + γs + κ are strictly negative when γ>0 and κ>0. -/
theorem charPoly_real_root_neg {gamma kappa s : ℝ}
    (hgamma : 0 < gamma) (hkappa : 0 < kappa)
    (hs : charPoly gamma kappa s = 0) : s < 0 := by
  have hpoly : s ^ 2 + gamma * s + kappa = 0 := by simpa [charPoly] using hs
  have hprod : s * (s + gamma) = -kappa := by nlinarith
  have hneg : s * (s + gamma) < 0 := by
    rw [hprod]
    exact neg_neg_of_pos hkappa
  by_contra hge
  push Not at hge
  have : 0 ≤ s * (s + gamma) :=
    mul_nonneg hge (le_of_lt (by linarith : 0 < s + gamma))
  exact absurd this (not_le.mpr hneg)

/-- Imaginary part of the characteristic equation: im · (2 re + γ) = 0. -/
theorem charPolyℂ_im_factor {gamma kappa : ℝ} {z : ℂ}
    (hz : charPolyℂ gamma kappa z = 0) :
    z.im * (2 * z.re + gamma) = 0 := by
  have him : (charPolyℂ gamma kappa z).im = 0 := by simp [hz]
  unfold charPolyℂ at him
  -- Expand: im(z² + γ z + κ) = 2 re im + γ im
  simp only [pow_two, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im] at him
  linarith

/-- Real part identity at a complex root. -/
theorem charPolyℂ_re_eq {gamma kappa : ℝ} {z : ℂ}
    (hz : charPolyℂ gamma kappa z = 0) :
    z.re ^ 2 - z.im ^ 2 + gamma * z.re + kappa = 0 := by
  have hre : (charPolyℂ gamma kappa z).re = 0 := by simp [hz]
  unfold charPolyℂ at hre
  simp only [pow_two, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im] at hre
  linarith

/-- TeX: thm:damped (spectral half) — every complex root has negative real part. -/
theorem thm_damped_spectral {gamma kappa : ℝ}
    (hgamma : 0 < gamma) (hkappa : 0 < kappa) :
    ∀ z : ℂ, charPolyℂ gamma kappa z = 0 → z.re < 0 := by
  intro z hz
  have hyfact := charPolyℂ_im_factor hz
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hyfact with him | hlin
  · have hre0 : z.re ^ 2 + gamma * z.re + kappa = 0 := by
      have := charPolyℂ_re_eq hz
      simp [him] at this
      linarith
    exact charPoly_real_root_neg hgamma hkappa (by simpa [charPoly] using hre0)
  · have : z.re = -gamma / 2 := by linarith
    linarith

/-- Envelope decay e^{-c t} → 0 for c > 0. -/
theorem tendsto_exp_neg_rate {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => Real.exp (-c * t)) atTop (nhds 0) := by
  have hmul : Tendsto (fun t : ℝ => c * t) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul).congr ?_
  intro t
  simp [Function.comp_apply, neg_mul]

/-- Overdamped linear solution A e^{r₁ t} + B e^{r₂ t} with rᵢ < 0. -/
theorem tendsto_overdamped {r1 r2 A B : ℝ} (h1 : r1 < 0) (h2 : r2 < 0) :
    Tendsto (fun t : ℝ => A * Real.exp (r1 * t) + B * Real.exp (r2 * t))
      atTop (nhds 0) := by
  have hA : Tendsto (fun t : ℝ => A * Real.exp (r1 * t)) atTop (nhds 0) := by
    have : (fun t : ℝ => Real.exp (r1 * t)) = fun t => Real.exp (- (-r1) * t) := by
      funext t; ring_nf
    simpa [this] using (tendsto_exp_neg_rate (neg_pos.mpr h1)).const_mul A
  have hB : Tendsto (fun t : ℝ => B * Real.exp (r2 * t)) atTop (nhds 0) := by
    have : (fun t : ℝ => Real.exp (r2 * t)) = fun t => Real.exp (- (-r2) * t) := by
      funext t; ring_nf
    simpa [this] using (tendsto_exp_neg_rate (neg_pos.mpr h2)).const_mul B
  simpa using hA.add hB

/-- Critically damped linear solution (A + B t) e^{-(γ/2) t}. -/
def criticalSol (gamma A B : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(gamma / 2) * t) * (A + B * t)

theorem tendsto_critical {gamma A B : ℝ} (hgamma : 0 < gamma) :
    Tendsto (criticalSol gamma A B) atTop (nhds 0) := by
  set α := gamma / 2
  have hαpos : 0 < α := by dsimp [α]; linarith
  have hA : Tendsto (fun t : ℝ => A * Real.exp (-α * t)) atTop (nhds 0) := by
    simpa using (tendsto_exp_neg_rate hαpos).const_mul A
  have hB : Tendsto (fun t : ℝ => B * t * Real.exp (-α * t)) atTop (nhds 0) := by
    have hpow := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hαt : Tendsto (fun t : ℝ => α * t) atTop atTop :=
      tendsto_id.const_mul_atTop hαpos
    have hcomp : Tendsto (fun t : ℝ => (α * t) * Real.exp (-(α * t))) atTop (nhds 0) := by
      have := hpow.comp hαt
      -- this : Tendsto ((fun x => x^1 * exp (-x)) ∘ (α * ·)) ...
      convert this using 1
      funext t
      simp [pow_one]
    have heq : (fun t : ℝ => B * t * Real.exp (-α * t)) =
        fun t => (B / α) * ((α * t) * Real.exp (-(α * t))) := by
      funext t
      have hα0 : α ≠ 0 := hαpos.ne'
      field_simp [hα0]
    rw [heq]
    simpa using hcomp.const_mul (B / α)
  have heq : criticalSol gamma A B =
      fun t => A * Real.exp (-α * t) + B * t * Real.exp (-α * t) := by
    funext t
    dsimp [criticalSol, α]
    ring
  rw [heq]
  simpa using hA.add hB

/-- Underdamped linear solution e^{-(γ/2)t}(A cos ωt + B sin ωt). -/
def underdampedSol (gamma A B omega : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(gamma / 2) * t) * (A * Real.cos (omega * t) + B * Real.sin (omega * t))

theorem abs_underdamped_le (gamma A B omega t : ℝ) :
    |underdampedSol gamma A B omega t| ≤
      (|A| + |B|) * Real.exp (-(gamma / 2) * t) := by
  unfold underdampedSol
  have hexp : 0 ≤ Real.exp (-(gamma / 2) * t) := (Real.exp_pos _).le
  have hcos : |Real.cos (omega * t)| ≤ 1 := abs_le.mpr
    ⟨Real.neg_one_le_cos (omega * t), Real.cos_le_one (omega * t)⟩
  have hsin : |Real.sin (omega * t)| ≤ 1 := abs_le.mpr
    ⟨Real.neg_one_le_sin (omega * t), Real.sin_le_one (omega * t)⟩
  have hosc :
      |A * Real.cos (omega * t) + B * Real.sin (omega * t)| ≤ |A| + |B| := by
    calc
      |A * Real.cos (omega * t) + B * Real.sin (omega * t)|
          ≤ |A * Real.cos (omega * t)| + |B * Real.sin (omega * t)| :=
        abs_add_le _ _
      _ = |A| * |Real.cos (omega * t)| + |B| * |Real.sin (omega * t)| := by
          simp [abs_mul]
      _ ≤ |A| * 1 + |B| * 1 := by
          gcongr
      _ = |A| + |B| := by ring
  calc
    |Real.exp (-(gamma / 2) * t) *
        (A * Real.cos (omega * t) + B * Real.sin (omega * t))|
        = Real.exp (-(gamma / 2) * t) *
            |A * Real.cos (omega * t) + B * Real.sin (omega * t)| := by
          rw [abs_mul, abs_of_nonneg hexp]
    _ ≤ Real.exp (-(gamma / 2) * t) * (|A| + |B|) := by gcongr
    _ = (|A| + |B|) * Real.exp (-(gamma / 2) * t) := by ring

theorem tendsto_underdamped {gamma A B omega : ℝ} (hgamma : 0 < gamma) :
    Tendsto (underdampedSol gamma A B omega) atTop (nhds 0) := by
  have hEnv : Tendsto (fun t : ℝ => (|A| + |B|) * Real.exp (-(gamma / 2) * t))
      atTop (nhds 0) := by
    simpa using (tendsto_exp_neg_rate (by linarith : 0 < gamma / 2)).const_mul (|A| + |B|)
  exact squeeze_zero_norm (fun t => abs_underdamped_le gamma A B omega t) hEnv

/-- TeX: thm:damped — spectral criterion plus decay of all standard linear solution forms. -/
theorem thm_damped (S : RestoringRemnant) :
    (∀ z : ℂ, charPolyℂ S.gamma S.kappa z = 0 → z.re < 0) ∧
      (∀ A B omega : ℝ, Tendsto (underdampedSol S.gamma A B omega) atTop (nhds 0)) ∧
      (∀ A B : ℝ, Tendsto (criticalSol S.gamma A B) atTop (nhds 0)) ∧
      (∀ r1 r2 A B : ℝ, r1 < 0 → r2 < 0 →
        Tendsto (fun t : ℝ => A * Real.exp (r1 * t) + B * Real.exp (r2 * t))
          atTop (nhds 0)) := by
  refine ⟨thm_damped_spectral S.hDamp S.kappa_pos, ?_, ?_, ?_⟩
  · intro A B omega; exact tendsto_underdamped S.hDamp
  · intro A B; exact tendsto_critical S.hDamp
  · intro r1 r2 A B h1 h2; exact tendsto_overdamped h1 h2

/-- Combined restoring criterion from the H' slope test. -/
theorem thm_restoring_from_Hprime {H' GM Rstar gamma : ℝ}
    (hR : 0 < Rstar) (hDamp : 0 < gamma)
    (hstr : H' < - (2 * GM / Rstar ^ 3)) :
    let S : RestoringRemnant :=
      { Rstar := Rstar
        Fprime := forceSlope H' GM Rstar
        gamma := gamma
        hR := hR
        hRest := lem_slope hstr
        hDamp := hDamp }
    (∀ z : ℂ, charPolyℂ S.gamma S.kappa z = 0 → z.re < 0) ∧
      (∀ A B omega : ℝ, Tendsto (underdampedSol S.gamma A B omega) atTop (nhds 0)) := by
  intro S
  exact ⟨(thm_damped S).1, (thm_damped S).2.1⟩

end

end Paper12
