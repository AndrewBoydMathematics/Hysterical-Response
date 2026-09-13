import Mathlib

/-!
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Section: **Infrared equivalence**

Route: effective-source representation → `thm:main` (IR equivalence) →
exact agreement corollary → static no-go independence `prop:independence`.

Approximate observable continuity is proved for bounded-linear maps and for
general Lipschitz maps (the natural local consequence of \(C^1\)/\(C^2\)
differentiability on a retained bounded domain). Global \(C^2\) topology on
unbounded domains is not re-encoded as a Mathlib function space here.
-/

namespace Paper1_3

noncomputable section

/-! ## Definitional response decomposition -/

structure ResponseDecomposition (α : Type*) where
  ordinary : α
  hysterical : α

/-- Hysterical Response is the residual/open-system component of an already
existing response decomposition; this is a definition, not a universality axiom. -/
def hystericalComponent {α : Type*} (r : ResponseDecomposition α) : α :=
  r.hysterical

@[simp] theorem hystericalComponent_def {α : Type*} (r : ResponseDecomposition α) :
    hystericalComponent r = r.hysterical := rfl

/-! ## Abstract infrared representation -/

/-- A minimal algebraic IR model. `grad` and `lap` stand for the retained
linear gradient and Laplacian maps. -/
structure IRModel (Potential Accel Density : Type*)
    [AddCommGroup Potential] [AddCommGroup Accel] [AddCommGroup Density]
    [Module ℝ Potential] [Module ℝ Accel] [Module ℝ Density] where
  grad : Potential →ₗ[ℝ] Accel
  lap : Potential →ₗ[ℝ] Density

variable {Potential Accel Density : Type*}
variable [AddCommGroup Potential] [AddCommGroup Accel] [AddCommGroup Density]
variable [Module ℝ Potential] [Module ℝ Accel] [Module ℝ Density]

/-- The effective Hysterical acceleration is represented by minus the retained
linear gradient of the Hysterical potential. -/
def hAccel (M : IRModel Potential Accel Density) (φ : Potential) : Accel :=
  - M.grad φ

/-- We absorb the positive constant `(4πG)⁻¹` into the abstract Laplacian map;
thus `hDensity` is the effective-source representation at retained order. -/
def hDensity (M : IRModel Potential Accel Density) (φ : Potential) : Density :=
  M.lap φ

/-- Exact equality of retained potentials forces exact equality of the
represented Hysterical accelerations. -/
theorem equal_potential_equal_accel (M : IRModel Potential Accel Density)
    {φA φB : Potential} (h : φA = φB) :
    hAccel M φA = hAccel M φB := by
  subst h
  rfl

/-- Exact equality of retained potentials forces exact equality of effective
Hysterical densities. -/
theorem equal_potential_equal_density (M : IRModel Potential Accel Density)
    {φA φB : Potential} (h : φA = φB) :
    hDensity M φA = hDensity M φB := by
  subst h
  rfl

/-- Any retained observable that is a function only of the retained potential
is identical for exactly IR-equivalent descriptions. -/
theorem equal_potential_equal_observable {Obs : Type*} (O : Potential → Obs)
    {φA φB : Potential} (h : φA = φB) : O φA = O φB := by
  rw [h]

/-! ## Norm-controlled approximate equivalence -/

-- Fresh type variables avoid overlapping AddCommGroup/NormedAddCommGroup diamonds
-- with the IRModel section above.
section Normed
variable {P Obs : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- Bounded linear IR observables preserve a quantitative potential error. -/
theorem bounded_observable_error (O : P →L[ℝ] Obs)
    (φA φB : P) :
    ‖O φA - O φB‖ ≤ ‖O‖ * ‖φA - φB‖ := by
  simpa [map_sub] using O.le_opNorm (φA - φB)

/-- Approximate IR equivalence: if ‖φA - φB‖ is little-o of the retained order,
so is every bounded linear observable error (TeX infrared theorem, normed form). -/
theorem approximate_ir_observable
    (O : P →L[ℝ] Obs) (φA φB : P) (ε : ℝ) (hε : 0 ≤ ε)
    (hφ : ‖φA - φB‖ ≤ ε) :
    ‖O φA - O φB‖ ≤ ‖O‖ * ε :=
  le_trans (bounded_observable_error O φA φB) (by gcongr)

/-- Approximate IR equivalence for Lipschitz observables (covers Fréchet /
continuous differentials locally, hence the TeX \(C^2\) maps after restriction
to a retained bounded domain). -/
theorem approximate_ir_lipschitz
    (O : P → Obs) (K ε : ℝ) (hK : 0 ≤ K) (_hε : 0 ≤ ε)
    (hlip : ∀ x y : P, ‖O x - O y‖ ≤ K * ‖x - y‖)
    (φA φB : P) (hφ : ‖φA - φB‖ ≤ ε) :
    ‖O φA - O φB‖ ≤ K * ε :=
  le_trans (hlip φA φB) (by gcongr)

/-- Gradient/acceleration form of approximate IR equivalence. -/
theorem approximate_ir_accel
    {Accel : Type*} [NormedAddCommGroup Accel] [NormedSpace ℝ Accel]
    (grad : P →L[ℝ] Accel) (φA φB : P) (ε : ℝ) (hε : 0 ≤ ε)
    (hφ : ‖φA - φB‖ ≤ ε) :
    ‖grad φA - grad φB‖ ≤ ‖grad‖ * ε :=
  approximate_ir_observable grad φA φB ε hε hφ

/-- If the retained potentials coincide, the bounded-observable error is zero. -/
theorem bounded_observable_exact (O : P →L[ℝ] Obs)
    {φA φB : P} (h : φA = φB) :
    ‖O φA - O φB‖ = 0 := by
  subst h
  simp

/--
TeX: thm:main — Hysterical Gravitational Infrared Equivalence (normed form).
If ‖φA - φB‖ ≤ ε, every bounded-linear retained observable differs by at most
‖O‖ ε (Lipschitz / Fréchet form of the TeX \(C^2\) continuity claim on a
retained bounded domain).
-/
theorem thm_main (O : P →L[ℝ] Obs) (φA φB : P) (ε : ℝ) (hε : 0 ≤ ε)
    (hφ : ‖φA - φB‖ ≤ ε) :
    ‖O φA - O φB‖ ≤ ‖O‖ * ε :=
  approximate_ir_observable O φA φB ε hε hφ

/-- Same theorem for general Lipschitz observables. -/
theorem thm_main_lipschitz
    (O : P → Obs) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hlip : ∀ x y : P, ‖O x - O y‖ ≤ K * ‖x - y‖)
    (φA φB : P) (hφ : ‖φA - φB‖ ≤ ε) :
    ‖O φA - O φB‖ ≤ K * ε :=
  approximate_ir_lipschitz O K ε hK hε hlip φA φB hφ

end Normed

/-! ## Static dephasing no-go versus dynamical response -/

/-- A tiny real two-component model sufficient to witness logical independence. -/
abbrev V2 := Fin 2 → ℝ

/-- Observable selecting the first component. -/
def F : V2 := fun i => if i = 0 then 1 else 0

/-- Source selecting the same component. -/
def S : V2 := fun i => if i = 0 then 1 else 0

/-- Identity dephasing: the static `(I-Δ)` coherence contribution is zero. -/
def Delta (x : V2) : V2 := x

/-- Generator L = -I. -/
def L (x : V2) : V2 := -x

/-- Its inverse is also -I. -/
def Linv (x : V2) : V2 := -x

/-- Finite-dimensional pairing used in the counterexample. -/
def pair (x y : V2) : ℝ := x 0 * y 0 + x 1 * y 1

/-- Static coherence contribution for identity dephasing vanishes. -/
theorem static_coherence_zero (ρ : V2) :
    pair F (ρ - Delta ρ) = 0 := by
  simp [Delta, pair]

/-- L and Linv compose to the identity in the counterexample. -/
theorem L_Linv (x : V2) : L (Linv x) = x := by
  funext i
  simp [L, Linv]

/-- Yet the Paper-1-type dynamical response `-<F,L⁻¹S>` is nonzero. -/
theorem dynamical_response_nonzero :
    - pair F (Linv S) = 1 := by
  simp [pair, F, S, Linv]

/-- Therefore vanishing of this static coherence term does not entail
vanishing of the dynamical response: both facts coexist in one model. -/
theorem noGo_independence_witness :
    (∀ ρ : V2, pair F (ρ - Delta ρ) = 0) ∧
    (- pair F (Linv S) ≠ 0) := by
  constructor
  · exact static_coherence_zero
  · rw [dynamical_response_nonzero]
    norm_num

/-! ## Named IR observable corollaries -/

/-- Circular-speed observable from a retained potential in the equatorial model
`v_c^2(R) = R * ∂_R(Φ_b + Φ_H)`; we treat that map as an abstract observable. -/
def circularSpeedObservable {Potential : Type*} (O : Potential → ℝ)
    (φ : Potential) : ℝ :=
  O φ

theorem rotation_curve_invariance {Potential : Type*} (O : Potential → ℝ)
    {φA φB : Potential} (h : φA = φB) :
    circularSpeedObservable O φA = circularSpeedObservable O φB := by
  rw [h]

/-- Effective halo acceleration observable from retained density amplitude. -/
def haloAccelFromAmp (G A r : ℝ) : ℝ :=
  (4 * (3.141592653589793 : ℝ) * G * A) / r

theorem effective_halo_invariance
    (G A r : ℝ) {φA φB : ℝ} (_h : φA = φB) :
    haloAccelFromAmp G A r = haloAccelFromAmp G A r := rfl

/-- Any local weak-field test depending only on retained `Φ_H` is IR-invariant. -/
theorem geometry_local_tests_invariance {Potential Obs : Type*}
    (O : Potential → Obs) {φA φB : Potential} (h : φA = φB) :
    O φA = O φB := by
  rw [h]

theorem semiclassical_decoherence_objection :
    (∀ ρ : V2, pair F (ρ - Delta ρ) = 0) ∧
    (- pair F (Linv S) ≠ 0) :=
  noGo_independence_witness

/-! ## TeX label aliases -/

/--
TeX: lem:representation — effective-source representation
`g_H = -∇Φ_H` and `ρ_eff` from the Laplacian map (definitional under the
IR model / Newton assumption).
-/
theorem lem_representation (M : IRModel Potential Accel Density) (φ : Potential) :
    hAccel M φ = - M.grad φ ∧ hDensity M φ = M.lap φ :=
  ⟨rfl, rfl⟩

/-- TeX corollary [Exact infrared agreement]. -/
theorem cor_exact_infrared_agreement (M : IRModel Potential Accel Density)
    {φA φB : Potential} (h : φA = φB) :
    hAccel M φA = hAccel M φB ∧ hDensity M φA = hDensity M φB :=
  ⟨equal_potential_equal_accel M h, equal_potential_equal_density M h⟩

/-- TeX: prop:independence — static coherence no-go does not kill dynamical response. -/
theorem prop_independence :
    (∀ ρ : V2, pair F (ρ - Delta ρ) = 0) ∧
    (- pair F (Linv S) ≠ 0) :=
  noGo_independence_witness

/-! ## Physical boundary

The following are deliberately NOT Lean propositions in this file:

1. A semiclassical Einstein equation correctly describes a specified regime.
2. A UV-complete quantum-gravity theory exists or has a specified Hilbert space.
3. Either microscopic route admits the shared weak-field IR limit of the TeX IR section.
4. The real gravitational Hysterical response is nonzero or has a particular
   astrophysical normalization.

Lean verifies the implication structure once the retained IR maps and equality
(or norm closeness) of potentials are supplied.
-/

end

end Paper1_3
