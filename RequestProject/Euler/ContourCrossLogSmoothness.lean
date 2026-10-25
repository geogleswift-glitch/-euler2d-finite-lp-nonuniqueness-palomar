module

public import RequestProject.Euler.ContourCrossLogDerivativeSmoothness
public import RequestProject.Euler.ContourCrossLogValueSmoothness
public import RequestProject.Euler.ContourC1SmoothnessCriterion

/-! Smoothness of the genuine cross-log map in the actual C¹ and little norms. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) crossCInfinityC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossCInfinityC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossCInfinityLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) crossCInfinityLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

variable {γ : ℝ≥0}

def contourCrossLogC1Shape (hγ1 : (γ : ℝ) ≤ 1)
    (p : ContourC1Space γ × ContourC1Space γ) : ContourC1Space γ := by
  classical
  exact if hp : ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ then
    contourCrossLogC1OnLocus hγ1 ⟨p, hp⟩ else 0

set_option maxHeartbeats 1000000 in
theorem contourCrossLogC1Shape_eq (hγ1 : (γ : ℝ) ≤ 1)
    (p : ContourC1Space γ × ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated p.1 p.2 σ) :
    contourCrossLogC1Shape hγ1 p = contourCrossLogC1 hγ1 p.1 p.2 hσ hsep := by
  rw [contourCrossLogC1Shape, dif_pos ⟨σ, hσ, hsep⟩]
  exact contourCrossLogC1OnLocus_eq hγ1 ⟨p, ⟨σ, hσ, hsep⟩⟩ hσ hsep

theorem contDiffOn_contourCrossLogC1Shape (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1) :
    ContDiffOn ℝ ∞ (contourCrossLogC1Shape hγ1)
      {p : ContourC1Space γ × ContourC1Space γ | ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ} := by
  apply (contDiffOn_contourC1_iff_baseDerivative (⊤ : ℕ∞)
    (isOpen_positiveSeparatedContourPairs γ) (contourCrossLogC1Shape hγ1)).mpr
  constructor
  · apply (contDiffOn_contourC1CrossLogIntegral_fixed hγ hγ1 0).congr
    rintro p ⟨σ, hσ, hsep⟩
    rw [contourCrossLogC1Shape_eq hγ1 p hσ hsep, lift_contourCrossLogC1]
  · apply (contDiffOn_contourCrossLogDerivativeShape hγ hγ1).congr
    rintro p ⟨σ, hσ, hsep⟩
    rw [contourCrossLogC1Shape_eq hγ1 p hσ hsep, derivative_contourCrossLogC1]
    exact (contourCrossLogDerivativeShape_eq hγ1 p.1 p.2 hσ hsep).symm

def contourLittlePairInclusion (γ : ℝ≥0) :
    (LittleContourSpace γ × LittleContourSpace γ) →L[ℝ] (ContourC1Space γ × ContourC1Space γ) :=
  ((LittleContourSpace.inclusion γ).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((LittleContourSpace.inclusion γ).comp (ContinuousLinearMap.snd ℝ _ _))

def contourCrossLogLittleShape (hγ1 : (γ : ℝ) ≤ 1)
    (p : LittleContourSpace γ × LittleContourSpace γ) : LittleContourSpace γ := by
  classical
  exact if hp : ∃ σ > 0, ContourCrossSeparated p.1.val p.2.val σ then
    contourCrossLogLittleOnLocus hγ1 ⟨p, hp⟩ else 0

theorem contourCrossLogLittleShape_eq (hγ1 : (γ : ℝ) ≤ 1)
    (p : PositiveSeparatedLittleContourPair γ) :
    contourCrossLogLittleShape hγ1 p.val = contourCrossLogLittleOnLocus hγ1 p := by
  rw [contourCrossLogLittleShape, dif_pos p.property]

set_option maxHeartbeats 1000000 in
theorem inclusion_contourCrossLogLittleShape (hγ1 : (γ : ℝ) ≤ 1)
    (p : LittleContourSpace γ × LittleContourSpace γ) :
    LittleContourSpace.inclusion γ (contourCrossLogLittleShape hγ1 p) =
      contourCrossLogC1Shape hγ1 (contourLittlePairInclusion γ p) := by
  by_cases hp : ∃ σ > 0, ContourCrossSeparated p.1.val p.2.val σ
  · rw [contourCrossLogLittleShape, dif_pos hp]
    change _ = contourCrossLogC1Shape hγ1 (p.1.val, p.2.val)
    rw [contourCrossLogC1Shape, dif_pos hp]
    rfl
  · have hl : contourCrossLogLittleShape hγ1 p = 0 := dif_neg hp
    have hr : contourCrossLogC1Shape hγ1 (p.1.val, p.2.val) = 0 := dif_neg hp
    change LittleContourSpace.inclusion γ (contourCrossLogLittleShape hγ1 p) =
      contourCrossLogC1Shape hγ1 (p.1.val, p.2.val)
    rw [hl, hr, map_zero]

theorem isOpen_positiveSeparatedLittleContourPairs (γ : ℝ≥0) :
    IsOpen {p : LittleContourSpace γ × LittleContourSpace γ |
      ∃ σ > 0, ContourCrossSeparated p.1.val p.2.val σ} :=
  (isOpen_positiveSeparatedContourPairs γ).preimage (contourLittlePairInclusion γ).continuous

theorem contDiffOn_contourCrossLogLittleShape (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1) :
    ContDiffOn ℝ ∞ (contourCrossLogLittleShape hγ1)
      {p : LittleContourSpace γ × LittleContourSpace γ |
        ∃ σ > 0, ContourCrossSeparated p.1.val p.2.val σ} := by
  let U : Set (LittleContourSpace γ × LittleContourSpace γ) :=
    {p | ∃ σ > 0, ContourCrossSeparated p.1.val p.2.val σ}
  have hi : ContDiffOn ℝ ∞
      (fun p => contourCrossLogC1Shape hγ1 (contourLittlePairInclusion γ p)) U :=
    (contDiffOn_contourCrossLogC1Shape hγ hγ1).comp
      (contourLittlePairInclusion γ).contDiff.contDiffOn (fun _ hp => hp)
  apply (contDiffOn_closedSubmodule_iff ((smoothContourSubmodule γ).topologicalClosure)
    (isClosed_littleContourSpace γ) (⊤ : ℕ∞) (isOpen_positiveSeparatedLittleContourPairs γ)
    (contourCrossLogLittleShape hγ1)).mp
  exact hi.congr (fun p _ => inclusion_contourCrossLogLittleShape hγ1 p)

end Euler2D

end
