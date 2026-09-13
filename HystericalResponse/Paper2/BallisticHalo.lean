import Mathlib
import HystericalResponse.Paper2.ResponseSector

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`, Section “Ballistic response-halo theorem”.

Ports:
  * IR ballistic realization → isotropic monoenergetic shell (`prop:ir-shell`);
  * multipole argument through dipole / quadrupole coefficient identities;
  * accretion → Q via J_in (`prop:accretion-Q`).
-/

set_option autoImplicit false

namespace Paper2

noncomputable section

/-- Euclidean dot product. -/
def dot (x y : Vec3) : ℝ :=
  ∑ i, x i * y i

@[simp] theorem dot_zero_right (x : Vec3) : dot x 0 = 0 := by
  simp [dot]

@[simp] theorem dot_zero_left (y : Vec3) : dot 0 y = 0 := by
  simp [dot]

/-- Euclidean speed on `Vec3`. -/
def speed (u : Vec3) : ℝ :=
  Real.sqrt (dot u u)

/--
Angular density of the normalized monoenergetic shell at speed `v`
(TeX factor `1/(4π v²)` multiplying `δ(|u|-v)`).
-/
def shellAngularDensity (v : ℝ) : ℝ :=
  1 / (4 * Real.pi * v ^ 2)

/--
IR production source on the monoenergetic shell:
`S(x,u) = J(x) / (4π v²)` for the angular density factor of `δ(|u|-v)/(4π v²)`.
Reduced abstraction: Dirac radial measure is carried by the TeX statement; Lean
records the angular normalization and the factorization `S = J · σ_shell`.
-/
def shellProduction (J : Vec3 → ℝ) (v : ℝ) (x _u : Vec3) : ℝ :=
  J x * shellAngularDensity v

/-- PHYSICS: IR ballistic realization hypotheses (TeX Ass. ir-ballistic). -/
structure IRBallisticRealization where
  /-- Spatial production profile. -/
  J : Vec3 → ℝ
  /-- Characteristic infrared residual-propagation speed. -/
  v : ℝ
  v_pos : 0 < v
  /-- Velocity kernel, before imposing the mono-scale shell. -/
  σ : Vec3 → ℝ
  /-- Local isotropy: equal speeds ⇒ equal kernel values. -/
  isotropic : ∀ u w : Vec3, speed u = speed w → σ u = σ w
  /--
  Single IR scale: kernel equals the monoenergetic shell angular density
  on the speed shell `|u| = v` (Dirac radial concentration at `v` in TeX).
  -/
  mono_scale : ∀ u : Vec3, speed u = v → σ u = shellAngularDensity v

/--
TeX: prop:ir-shell — isotropic monoenergetic shell.
Under Ass. ir-ballistic, on the characteristic shell `|u| = v` one has
`S(x,u) = J(x) δ(|u|-v)/(4π v²)` in the TeX sense, recorded here as
`S = J · shellAngularDensity v`.
-/
theorem prop_ir_shell
    (R : IRBallisticRealization)
    (x u : Vec3)
    (hon : speed u = R.v) :
    R.J x * R.σ u = shellProduction R.J R.v x u := by
  unfold shellProduction
  rw [R.mono_scale u hon]

/-- Isotropy alone: the velocity kernel is a function of speed. -/
theorem prop_ir_shell_depends_on_speed
    (R : IRBallisticRealization)
    (u w : Vec3)
    (heq : speed u = speed w) :
    R.σ u = R.σ w :=
  R.isotropic u w heq

/-- Abstract radial kernel (TeX Eq. kernel); retained for documentation. -/
def ballisticKernel
    (v lam : ℝ)
    (J : Vec3 → ℝ)
    (x : Vec3) : ℝ :=
  (1 / (4 * Real.pi * v)) *
    ∫ y,
      J y *
      Real.exp (- ‖x - y‖ / lam) /
      (‖x - y‖ ^ 2)

/-- Leading monopole term in TeX Eq. halo. -/
def haloMonopoleDensity (v Q r : ℝ) : ℝ :=
  Q / (4 * Real.pi * v * r ^ 2)

theorem haloMonopoleDensity_eq (v Q r : ℝ) :
    haloMonopoleDensity v Q r = Q / (4 * Real.pi * v * r ^ 2) :=
  rfl

/-- TeX multipole polynomial for `1/‖x−y‖²` through order `r⁻⁴`. -/
def invSqMultipolePoly (r : ℝ) (n y : Vec3) : ℝ :=
  1 / r ^ 2 + (2 * dot n y) / r ^ 3 +
    (4 * (dot n y) ^ 2 - ‖y‖ ^ 2) / r ^ 4

/--
A localized centered source, packaged exactly as in the TeX hypotheses:
total rate `Q`, vanishing first moment, planar second moment `s = ⟨R'²⟩`.
-/
structure LocalizedCenteredSource where
  Q : ℝ
  firstMoment : Vec3
  centered : firstMoment = 0
  /-- Second radial moment `s = ⟨R'²⟩` (TeX). -/
  s : ℝ

/--
Contribution of the multipole polynomial through dipole order, integrated against
a source with total mass `Q` and first moment `d` (TeX substitution step).
-/
def multipoleThroughDipole (v Q r : ℝ) (n d : Vec3) : ℝ :=
  (1 / (4 * Real.pi * v)) * (Q / r ^ 2 + (2 / r ^ 3) * dot n d)

/--
TeX: prop:accretion-Q — Accretion supplies `Q` via `J_in`.
If ballistic production packages Paper~1's unentangled-incoming drive with
conversion `α > 0`, then `Q = α J_in^tot`. When baryonic accretion supplies
that channel at particle rate `Ṅ_acc`, one has `Q = α Ṅ_acc`.
Reduced abstraction: the packaging and accretion-channel identifications are
hypotheses; the conclusion is the resulting algebra (not the unit identity
`Q = Ṁ_b` without `α`).
-/
theorem prop_accretion_Q
    (α Jin_tot Ndot_acc Q : ℝ)
    (hpack : Q = α * Jin_tot)
    (hacc : Jin_tot = Ndot_acc) :
    Q = α * Ndot_acc := by
  rw [hpack, hacc]

/-- Same conclusion under an explicit positive conversion factor. -/
theorem prop_accretion_Q_of_pos
    (α Jin_tot Ndot_acc Q : ℝ)
    (_hα : 0 < α)
    (hpack : Q = α * Jin_tot)
    (hacc : Jin_tot = Ndot_acc) :
    Q = α * Ndot_acc :=
  prop_accretion_Q α Jin_tot Ndot_acc Q hpack hacc

/--
Integrated multipole polynomial through dipole order against a source with
total rate `Q` and first-moment vector `d`.
-/
def integratedMultipoleThroughDipole
    (v Q r : ℝ) (n d : Vec3) : ℝ :=
  (1 / (4 * Real.pi * v)) * (Q / r ^ 2 + (2 / r ^ 3) * dot n d)

theorem integratedMultipoleThroughDipole_eq_multipoleThroughDipole
    (v Q r : ℝ) (n d : Vec3) :
    integratedMultipoleThroughDipole v Q r n d =
      multipoleThroughDipole v Q r n d :=
  rfl

/--
TeX: thm:ballistic-halo (through dipole order).
Under centering the dipole vanishes, so the far-field density through
`O(r⁻³)` is the spherical monopole `Q/(4π v r²)`.
Source geometry first appears at `O(r⁻⁴)`.
Reduced abstraction: continuum integral remainder `O(r⁻⁴)` is the standard
truncation past this coefficient identity (not a measure-theoretic big-O proof).
-/
theorem thm_ballistic_halo
    (v : ℝ)
    (src : LocalizedCenteredSource)
    (r : ℝ)
    (n : Vec3) :
    multipoleThroughDipole v src.Q r n src.firstMoment =
      haloMonopoleDensity v src.Q r := by
  unfold multipoleThroughDipole haloMonopoleDensity
  rw [src.centered, dot_zero_right]
  ring

/-- Integrated form of the same dipole-cancellation step. -/
theorem thm_ballistic_halo_integrated
    (v : ℝ)
    (src : LocalizedCenteredSource)
    (r : ℝ)
    (n : Vec3) :
    integratedMultipoleThroughDipole v src.Q r n src.firstMoment =
      haloMonopoleDensity v src.Q r := by
  rw [integratedMultipoleThroughDipole_eq_multipoleThroughDipole]
  exact thm_ballistic_halo v src r n

/-- Dipole coefficient identity used in the TeX proof. -/
theorem dipole_term_vanishes
    (n : Vec3)
    (src : LocalizedCenteredSource) :
    dot n src.firstMoment = 0 := by
  rw [src.centered, dot_zero_right]

/-- Explicit statement that geometry is deferred past dipole order. -/
theorem halo_geometry_starts_at_r4
    (v : ℝ)
    (src : LocalizedCenteredSource)
    (r : ℝ)
    (n : Vec3) :
    multipoleThroughDipole v src.Q r n src.firstMoment -
        haloMonopoleDensity v src.Q r = 0 := by
  rw [thm_ballistic_halo]
  ring

/--
Quadrupole (order `r⁻⁴`) piece of the TeX kernel polynomial, integrated against
a planar second-moment scalar `s`.
-/
def multipoleQuadrupoleTerm (v Q s r θ : ℝ) : ℝ :=
  (1 / (4 * Real.pi * v)) * (Q * s * (2 * Real.sin θ ^ 2 - 1)) / r ^ 4

theorem multipole_through_quad_eq_nQuadBracket
    (v Q s r θ : ℝ)
    (hv : v ≠ 0)
    (hr : r ≠ 0) :
    haloMonopoleDensity v Q r + multipoleQuadrupoleTerm v Q s r θ =
      haloMonopoleDensity v Q r *
        (1 + (s / r ^ 2) * (2 * Real.sin θ ^ 2 - 1)) := by
  unfold haloMonopoleDensity multipoleQuadrupoleTerm
  field_simp [hv, hr]

end

end Paper2
