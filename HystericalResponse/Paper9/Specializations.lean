/-
TeX: `9_branch_asymmetry_master/paper_9_branch_asymmetry_master.tex`
Channel specializations: each corollary is the master theorem under a named
portal/kernel identification (physical inputs, not uniqueness claims).
-/

import Mathlib
import HystericalResponse.Paper9.MasterAsymmetry

set_option autoImplicit false

namespace Paper9

noncomputable section

/-- Named channel: same algebra, documentation tag for TeX corollaries. -/
structure Channel where
  /-- Nonzero portal/source coefficient κ. -/
  κ : ℝ
  hκ : 0 < κ

/-- Apply master asymmetry in a named channel. -/
theorem channel_asymmetry
    (ch : Channel) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf ch.κ kernel h ≠ 0 ∧
      eta Φf ch.κ kernel (oppositeHistory h) ≠ 0 ∧
      eta Φf ch.κ kernel (oppositeHistory h) = -eta Φf ch.κ kernel h :=
  thm_master_asymmetry Φf ch.κ ch.hκ kernel h hmono hoverlap

/-! ### Concrete channel tags (TeX corollaries) -/

/-- Electroweak baryon / Y W̃W channel tag. -/
def channel_baryon (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_baryon
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Gravitational B−L / Y R̃R channel tag. -/
def channel_bl (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_bl
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Strong CP / θ : Y G̃G. -/
def channel_strongCP (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_strongCP
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Magnetic / hypermagnetic helicity. -/
def channel_magHelicity (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_magHelicity
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Gravitational-wave chirality. -/
def channel_gwChirality (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_gwChirality
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Cosmic birefringence / parity-odd polarization rotation. -/
def channel_birefringence (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_birefringence
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Asymmetric dark matter (dark anomalous portal). -/
def channel_ADM (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_ADM
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Affleck–Dine condensate phase. -/
def channel_AffleckDine (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_AffleckDine
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Axion misalignment sign. -/
def channel_axionMisalign (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_axionMisalign
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Chiral magnetic / axial charge. -/
def channel_CME (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_CME
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Dark ℤ₂ / mirror imbalance. -/
def channel_darkZ2 (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_darkZ2
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Weak parity / left–right parent channel (TeX Model LR; speculative BSM). -/
def channel_weakParity (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_weakParity_parent
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

/-- Topological defect / winding bias. -/
def channel_defectBias (κ : ℝ) (hκ : 0 < κ) : Channel := ⟨κ, hκ⟩

theorem cor_defectBias
    (κ : ℝ) (hκ : 0 < κ) (Φf : FreezeoutFunctional)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 :=
  cor_labeling Φf κ hκ kernel h hmono hoverlap

end
end Paper9
