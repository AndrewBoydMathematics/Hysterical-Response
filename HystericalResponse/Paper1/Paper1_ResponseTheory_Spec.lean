import Mathlib

/-
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Sections: **Setup: states, dephasing, and Newtonian geometry**
and the Banach core of **Constructive response theory**
(`thm:resolvent-response`, stable Laplace integral, two-level `|B|≤|δf|/2`).

Channel-sector / mixing / symmetry / coherence-norm ports that complete the
constructive section live in `ConstructiveResponse.lean` (TeX order after the
resolvent theorem).

Literature: `literature_c0_resolvent_laplace` (Pazy / Engel–Nagel).
Physical: `physics_open_system_model_is_applicable`.
-/

set_option autoImplicit false

open scoped NNReal

namespace Paper1

noncomputable section

/-! ## 1. Abstract response interface -/

variable {State Obs V : Type*}
variable [AddCommGroup V]

-- Evaluation of an observable on a state (`Tr[F ρ]` in the concrete paper).
variable (eval : Obs → State → V)

-- Localization/dephasing map on states.
variable (Δ : State → State)

/-- Coherent contribution relative to a chosen dephasing. -/
def coherentForce (F : Obs) (ρ : State) : V :=
  eval F ρ - eval F (Δ ρ)

/-- Paper-1 no-go theorem at the abstract observable level:
    if dephasing leaves the force expectation invariant, its "coherent"
    contribution vanishes. -/
theorem coherentForce_eq_zero
    (F : Obs) (ρ : State)
    (hdiag : eval F ρ = eval F (Δ ρ)) :
    coherentForce eval Δ F ρ = 0 := by
  simp [coherentForce, hdiag]

/--
TeX: Lemma [Ensemble linearity].
If force evaluation and dephasing are linear in the state, both the total
force and the dephasing-relative coherence commute with finite ensemble means.
-/
theorem lem_ensemble_linearity
    {n : ℕ} [AddCommGroup State] [Module ℝ State] [Module ℝ V]
    (F : Obs) (w : Fin n → ℝ) (ρ : Fin n → State)
    (hlin : ∀ (c : Fin n → ℝ) (σ : Fin n → State),
      eval F (∑ i, c i • σ i) = ∑ i, c i • eval F (σ i))
    (hΔ : ∀ (c : Fin n → ℝ) (σ : Fin n → State),
      Δ (∑ i, c i • σ i) = ∑ i, c i • Δ (σ i)) :
    eval F (∑ i, w i • ρ i) = ∑ i, w i • eval F (ρ i) ∧
      coherentForce eval Δ F (∑ i, w i • ρ i) =
        ∑ i, w i • coherentForce eval Δ F (ρ i) := by
  refine ⟨hlin w ρ, ?_⟩
  have hmean := hlin w ρ
  have hD := hΔ w ρ
  have hlinΔ := hlin w (fun i => Δ (ρ i))
  calc
    coherentForce eval Δ F (∑ i, w i • ρ i)
        = eval F (∑ i, w i • ρ i) - eval F (Δ (∑ i, w i • ρ i)) := rfl
    _ = (∑ i, w i • eval F (ρ i)) - eval F (∑ i, w i • Δ (ρ i)) := by
        rw [hmean, hD]
    _ = (∑ i, w i • eval F (ρ i)) - ∑ i, w i • eval F (Δ (ρ i)) := by
        rw [hlinΔ]
    _ = ∑ i, w i • (eval F (ρ i) - eval F (Δ (ρ i))) := by
        simp [Finset.sum_sub_distrib, smul_sub]
    _ = ∑ i, w i • coherentForce eval Δ F (ρ i) := by
        simp [coherentForce]

/-! ## 2. Stationary open-system response -/

variable {X : Type*}
variable [AddCommGroup X]

/-- Abstract inverse-generator representation of the stationary response. -/
def stationaryResponse (Linv : X → X) (S : X) : X :=
  - Linv S

open MeasureTheory Set

/-- Formal semigroup data used by the concrete trace-class realization. -/
structure StableSemigroupData (X : Type*) [NormedAddCommGroup X] where
  evolve : NNReal → X → X
  M : ℝ
  γ : ℝ
  M_pos : 0 < M
  γ_pos : 0 < γ
  exponential_bound :
    ∀ (t : NNReal) (x : X),
      ‖evolve t x‖ ≤ M * Real.exp (-γ * (t : ℝ)) * ‖x‖
  /-- Strong measurability of real-time orbits (needed for Bochner integration). -/
  aestronglyMeasurable_orbit :
    ∀ x : X,
      AEStronglyMeasurable (fun t : ℝ => evolve (Real.toNNReal t) x)
        (volume.restrict (Ioi (0 : ℝ)))

/-- Orbit of a source under the stable semigroup, as a real-time path. -/
def StableSemigroupData.orbit {X : Type*} [NormedAddCommGroup X]
    (data : StableSemigroupData X) (S : X) : ℝ → X :=
  fun t => data.evolve (Real.toNNReal t) S

theorem StableSemigroupData.aestronglyMeasurable_orbit_eq
    {X : Type*} [NormedAddCommGroup X]
    (data : StableSemigroupData X) (S : X) :
    AEStronglyMeasurable (data.orbit S) (volume.restrict (Ioi (0 : ℝ))) :=
  data.aestronglyMeasurable_orbit S

/-- Pointwise exponential envelope on `(0, ∞)`. -/
theorem StableSemigroupData.norm_orbit_le {X : Type*} [NormedAddCommGroup X]
    (data : StableSemigroupData X) (S : X) {t : ℝ} (ht : 0 < t) :
    ‖data.orbit S t‖ ≤ data.M * Real.exp (-data.γ * t) * ‖S‖ := by
  have ht' : (Real.toNNReal t : ℝ) = t := Real.coe_toNNReal t ht.le
  simpa [StableSemigroupData.orbit, ht'] using data.exponential_bound (Real.toNNReal t) S

/-- Integrable scalar envelope `t ↦ M e^{-γ t} ‖S‖` on `(0, ∞)`. -/
theorem StableSemigroupData.integrable_envelope {X : Type*} [NormedAddCommGroup X]
    (data : StableSemigroupData X) (S : X) :
    IntegrableOn (fun t : ℝ => data.M * Real.exp (-data.γ * t) * ‖S‖) (Ioi (0 : ℝ)) := by
  have hExp : IntegrableOn (fun t : ℝ => Real.exp (-data.γ * t)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (a := -data.γ) (neg_lt_zero.mpr data.γ_pos) (0 : ℝ)
  have h : IntegrableOn (fun t : ℝ => (data.M * ‖S‖) * Real.exp (-data.γ * t)) (Ioi (0 : ℝ)) :=
    hExp.const_mul (data.M * ‖S‖)
  exact h.congr (Filter.Eventually.of_forall fun _ => by ring)

/-- Exponential decay dominates the orbit, so the Bochner integral converges.

Literature (not an original research claim): for a \(C_0\)-semigroup with
generator \(A\) and growth bound \(\omega_0\), the resolvent is the Laplace
transform
  \(R(\lambda,A)x=\int_0^\infty e^{-\lambda t}T(t)x\,dt\)
whenever \(\operatorname{Re}\lambda>\omega_0\)
(Pazy, *Semigroups of Linear Operators and Applications to PDEs*;
Engel–Nagel, *One-Parameter Semigroups for Linear Evolution Equations*).
Under exponential stability this specializes to
  \((-A)^{-1}x=\int_0^\infty T(t)x\,dt\).
Mathlib does not yet package that unbounded-generator identification, so here
the stable Laplace integral *defines* the response resolvent used by Paper 1. -/
theorem StableSemigroupData.integrable_orbit {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (data : StableSemigroupData X) (S : X) :
    IntegrableOn (data.orbit S) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (data.integrable_envelope S) (data.aestronglyMeasurable_orbit_eq S) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact data.norm_orbit_le S ht

/-- Resolvent / Laplace representation: `-L⁻¹ S := ∫₀^∞ e^{tL} S dt`. -/
def StableSemigroupData.resolventIntegral {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X]
    (data : StableSemigroupData X) (S : X) : X :=
  ∫ t in Ioi (0 : ℝ), data.orbit S t

/-- Inverse-generator map induced by exponential stability. -/
def StableSemigroupData.Linv {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X]
    (data : StableSemigroupData X) (S : X) : X :=
  - data.resolventIntegral S

/-- Under exponential stability, the stationary response equals the Bochner
Laplace integral of the semigroup orbit. -/
theorem inverse_generator_as_semigroup_integral
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (data : StableSemigroupData X) (S : X) :
    stationaryResponse data.Linv S =
      ∫ t in Ioi (0 : ℝ), data.orbit S t := by
  simp [stationaryResponse, StableSemigroupData.Linv, StableSemigroupData.resolventIntegral]

/-- Susceptibility bound `‖χ‖ ≤ M/γ` at the Banach-space level. -/
theorem StableSemigroupData.norm_resolventIntegral_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (data : StableSemigroupData X) (S : X) :
    ‖data.resolventIntegral S‖ ≤ (data.M / data.γ) * ‖S‖ := by
  have hdom :
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        ‖data.orbit S t‖ ≤ data.M * Real.exp (-data.γ * t) * ‖S‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact data.norm_orbit_le S ht
  have hscal := data.integrable_envelope S
  have hγ : data.γ ≠ 0 := data.γ_pos.ne'
  refine (norm_integral_le_of_norm_le hscal hdom).trans (le_of_eq ?_)
  have hEq :
      (fun t : ℝ => data.M * Real.exp (-data.γ * t) * ‖S‖) =
        fun t : ℝ => (data.M * ‖S‖) * Real.exp (-data.γ * t) := by
    funext t; ring
  rw [hEq, integral_const_mul]
  have hInt := integral_exp_mul_Ioi (a := -data.γ) (neg_lt_zero.mpr data.γ_pos) (0 : ℝ)
  have hval : ∫ t in Ioi (0 : ℝ), Real.exp (-data.γ * t) = data.γ⁻¹ := by
    -- `integral_exp_mul_Ioi` writes the exponent as `-(γ * t)`.
    simpa [neg_mul, Real.exp_zero, hγ] using hInt
  rw [hval]
  field_simp [hγ]

/-! ## 3. Channel decomposition -/

/-- Linear response functional. -/
def responseForce
    (evalF : X → V)
    (Linv : X → X)
    (S : X) : V :=
  evalF (- Linv S)

/-- Continuum channel source `S = ∫ J(ξ) • Sξ dμ`. -/
def channelSource {α : Type*} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [MeasurableSpace α] (μ : Measure α)
    (J : α → ℝ) (Sξ : α → Y) : Y :=
  ∫ ξ, J ξ • Sξ ξ ∂μ

/-- Linearity of the response map in an ℝ-scaled source. -/
theorem responseForce_smul
    {Y W : Type*} [AddCommGroup Y] [AddCommGroup W]
    [Module ℝ Y] [Module ℝ W]
    (evalF : Y → W) (Linv : Y → Y) (c : ℝ) (S : Y)
    (hL : Linv (c • S) = c • Linv S)
    (hE : ∀ y, evalF (c • y) = c • evalF y) :
    responseForce (X := Y) (V := W) evalF Linv (c • S) =
      c • responseForce (X := Y) (V := W) evalF Linv S := by
  simp [responseForce, hL]
  -- `-(c • Linv S) = c • (-Linv S)`, then apply `hE`.
  rw [← smul_neg, hE]

/-- Additivity of the response map under an additive resolvent. -/
theorem responseForce_add
    {Y W : Type*} [AddCommGroup Y] [AddCommGroup W]
    (evalF : Y → W) (Linv : Y → Y) (S₁ S₂ : Y)
    (hL : Linv (S₁ + S₂) = Linv S₁ + Linv S₂)
    (hE : ∀ x y, evalF (x + y) = evalF x + evalF y) :
    responseForce (X := Y) (V := W) evalF Linv (S₁ + S₂) =
      responseForce (X := Y) (V := W) evalF Linv S₁ +
        responseForce (X := Y) (V := W) evalF Linv S₂ := by
  simp [responseForce, hL, hE, neg_add_rev]
  abel

/-! ## 4. Solvable two-level block -/

/-- Two-level energy splitting Ω = √(4κ² + Δ²). -/
def Omega (κ ΔE : ℝ) : ℝ :=
  Real.sqrt (4 * κ^2 + ΔE^2)

/-- Davies-equilibrium z-component used in the paper. -/
def rzEq (β κ ΔE : ℝ) : ℝ :=
  -(ΔE / Omega κ ΔE) * Real.tanh (β * Omega κ ΔE / 2)

/-- Population-force bias. -/
def populationBias (β κ ΔE δf : ℝ) : ℝ :=
  -(δf * ΔE / (2 * Omega κ ΔE)) *
    Real.tanh (β * Omega κ ΔE / 2)

/-- Under Ω > 0, `|B| ≤ |δf|/2` using `|ΔE|/Ω ≤ 1` and `|tanh x| < 1`. -/
theorem populationBias_bound
    (β κ ΔE δf : ℝ)
    (hOmega : 0 < Omega κ ΔE) :
    |populationBias β κ ΔE δf| ≤ |δf| / 2 := by
  set Ω := Omega κ ΔE with hΩdef
  have hΩpos : 0 < Ω := hOmega
  have hΩ0 : Ω ≠ 0 := ne_of_gt hΩpos
  -- Rewrite the bias into a product form that makes the bound obvious.
  have hfactor :
      populationBias β κ ΔE δf =
        (δf / 2) * (-(ΔE / Ω) * Real.tanh (β * Ω / 2)) := by
    dsimp [populationBias]
    rw [← hΩdef]
    ring
  have hRatio : |ΔE| / Ω ≤ 1 := by
    have hsq : ΔE ^ 2 ≤ 4 * κ ^ 2 + ΔE ^ 2 := by nlinarith [sq_nonneg κ]
    have : |ΔE| ≤ Ω := by
      have h1 : |ΔE| = Real.sqrt (ΔE ^ 2) := (Real.sqrt_sq_eq_abs ΔE).symm
      rw [h1, show Ω = Real.sqrt (4 * κ ^ 2 + ΔE ^ 2) from hΩdef]
      exact Real.sqrt_le_sqrt hsq
    exact (div_le_one hΩpos).2 this
  have htanh : |Real.tanh (β * Ω / 2)| ≤ 1 :=
    le_of_lt (Real.abs_tanh_lt_one _)
  rw [hfactor]
  have habs :
      |(δf / 2) * (-(ΔE / Ω) * Real.tanh (β * Ω / 2))| =
        (|δf| / 2) * (|ΔE| / Ω * |Real.tanh (β * Ω / 2)|) := by
    have hdiv : |ΔE / Ω| = |ΔE| / Ω := by
      rw [abs_div, abs_of_pos hΩpos]
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), hdiv]
  rw [habs]
  have hprod : |ΔE| / Ω * |Real.tanh (β * Ω / 2)| ≤ 1 := by
    have := mul_le_mul hRatio htanh (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  calc
    (|δf| / 2) * (|ΔE| / Ω * |Real.tanh (β * Ω / 2)|)
        ≤ (|δf| / 2) * 1 := by gcongr
    _ = |δf| / 2 := by ring

/-! ## 5. Renewal-response reduction -/

/-- Renewal prefactor multiplying the single-event bias. -/
def renewalPrefactor
    (J Γem Γfr : ℝ) : ℝ :=
  (J / Γem) * (Γfr / (Γfr + Γem))

def renewalResponse
    (J Γem Γfr B : ℝ) : ℝ :=
  renewalPrefactor J Γem Γfr * B

/-! ## 6. Newtonian number-density geometry -/

/-- Euclidean configuration space used by the Newtonian formulas. -/
abbrev Euclidean3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Kernel for the Newtonian potential, regularized by `0` on the diagonal. -/
def newtonKernel (x y : Euclidean3) : ℝ :=
  if x = y then 0 else ‖x - y‖⁻¹

/-- Kernel for the Newtonian field, regularized by `0` on the diagonal. -/
def newtonFieldKernel (x y : Euclidean3) : Euclidean3 :=
  if x = y then 0 else (‖x - y‖ ^ 3)⁻¹ • (x - y)

/-- Total particle number `N = ∫ K`. -/
def totalNumber (K : Euclidean3 → ℝ) : ℝ :=
  ∫ y, K y

/-- Newtonian potential
`Φ(x) = -G m ∫ K(y)/|x-y| dy`
at points where the integral exists. -/
def newtonianPotential (G m : ℝ) (K : Euclidean3 → ℝ) (x : Euclidean3) : ℝ :=
  -G * m * ∫ y, K y * newtonKernel x y

/-- Newtonian field
`g(x) = -G m ∫ K(y)(x-y)/|x-y|³ dy`
at points where the Bochner integral exists. -/
def newtonianField (G m : ℝ) (K : Euclidean3 → ℝ) (x : Euclidean3) : Euclidean3 :=
  -(G * m) • ∫ y, K y • newtonFieldKernel x y

/-- Potential is homogeneous of degree one in the number density. -/
theorem newtonianPotential_smul (G m c : ℝ) (K : Euclidean3 → ℝ) (x : Euclidean3) :
    newtonianPotential G m (fun y => c * K y) x =
      c * newtonianPotential G m K x := by
  simp only [newtonianPotential]
  have h :
      (fun y : Euclidean3 => (c * K y) * newtonKernel x y) =
        fun y => c * (K y * newtonKernel x y) := by
    funext y; ring
  rw [h, integral_const_mul]
  ring

/-- Field is homogeneous of degree one in the number density. -/
theorem newtonianField_smul (G m c : ℝ) (K : Euclidean3 → ℝ) (x : Euclidean3) :
    newtonianField G m (fun y => c * K y) x =
      c • newtonianField G m K x := by
  simp only [newtonianField]
  have h :
      (fun y : Euclidean3 => (c * K y) • newtonFieldKernel x y) =
        fun y => c • (K y • newtonFieldKernel x y) := by
    funext y; simp [smul_smul, mul_comm]
  rw [h, integral_smul]
  simp only [smul_smul]
  congr 1
  ring

/-! ## 7. Physical interpretation boundary -/

/-- PHYSICS POSTULATE PLACEHOLDER:
    the concrete response sector and its source `S` represent the physical
    open-system mechanism being modeled.  Lean can verify consequences of
    this model; it cannot establish that Nature chooses this model. -/
axiom physics_open_system_model_is_applicable : Prop

/-! ## Literature hypothesis: C₀ resolvent–Laplace identity

Pazy / Engel–Nagel: for a C₀-semigroup with generator `A` and growth bound
`ω₀`, `R(λ,A) = ∫₀^∞ e^{-λ t} T(t) dt` whenever `Re λ > ω₀`. Under exponential
stability this specializes to `(-A)⁻¹ = ∫₀^∞ T(t) dt`.

Lean constructs and bounds that integral under `StableSemigroupData`. The
identification with the unbounded-generator resolvent is this literature
hypothesis — not a silent `sorry`.
-/
axiom literature_c0_resolvent_laplace : Prop

end

end Paper1
