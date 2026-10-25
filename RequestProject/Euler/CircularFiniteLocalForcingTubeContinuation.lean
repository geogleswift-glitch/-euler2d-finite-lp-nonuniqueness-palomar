module

public import RequestProject.Euler.CircularFinitePhaseFieldBound
public import RequestProject.Euler.CircularFiniteLocalForcingContinuation
public import RequestProject.Euler.CircularAncientFiniteInitialFamily

/-! Strict actual circular phase bounds prevent a finite material
trajectory from stopping at a finite time. A genuine Banach limit and
the same forcing produce an extension of the original path. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) circularLocalTubeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularLocalTubeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularLocalTubeC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem exists_finiteCircular_phase_tube_continuation_local_forcing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ η a D H ME : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρa : ρ ≤ cellA / 4)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    (ha : 0 < a) (hsize : R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4)
    (hD : 0 < D) (hH : 0 < H) (hME : 0 ≤ ME) {N : ℕ}
    (g : FiniteCircularIndex N → ℝ)
    (E : ℝ → (FiniteCircularIndex N → LittleContourSpace γ) →
      FiniteCircularIndex N → LittleContourSpace γ)
    (hElocal : ∀ W : FiniteCircularIndex N → LittleContourSpace γ,
      IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) W → ‖W‖ < a / 4 →
      ∃ K : ℝ≥0, ∃ V : Set (FiniteCircularIndex N → LittleContourSpace γ),
        V ∈ 𝓝 W ∧ (∀ t, LipschitzOnWith K (E t) V) ∧
          ∀ Z ∈ V, Continuous (fun t => E t Z))
    (hEbound : ∀ t ∈ Icc (0 : ℝ) D, ∀ W : FiniteCircularIndex N → LittleContourSpace γ,
      (∃ b : FiniteCircularIndex N → ℝ, ∀ p,
        ‖contourParameterShiftC1 (b p) (W p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1) → ‖E t W‖ ≤ ME)
    (Z : ℝ → FiniteCircularIndex N → LittleContourSpace γ)
    (hd : ∀ t ∈ Ico (0 : ℝ) D, HasDerivAt Z
      (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g (Z t) + E t (Z t)) t)
    (hmem : ∀ t ∈ Ico (0 : ℝ) D,
      IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (Z t) ∧ ‖Z t‖ < a / 4 ∧
      IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (Z t))
    (htube : ∀ t ∈ Ioo (0 : ℝ) D, ∃ b : FiniteCircularIndex N → ℝ, ∀ p,
      ‖contourParameterShiftC1 (b p) (Z t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
        η * radScale R ρ p.1) :
    ∃ δ > 0, δ ≤ H ∧ ∃ Y : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
      (∀ t ∈ Ico (0 : ℝ) D, Y t = Z t) ∧
      ContinuousOn Y (Icc (0 : ℝ) (D + δ)) ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ), HasDerivAt Y
        (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g (Y t) + E t (Y t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ),
        IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Y t) ∧ ‖Y t‖ < a / 4 ∧
        IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Y t)) ∧
      ∀ t ∈ Icc (0 : ℝ) (D + δ), ∀ i θ,
        HasDerivAt (fun s => LittleContourSpace.lift γ (Y s i) θ)
          (contourBoundaryField g (fun j => LittleContourSpace.lift γ (Y t j)) i θ +
            LittleContourSpace.lift γ (E t (Y t) i) θ) t := by
  obtain ⟨B, hB, hBound⟩ := exists_finiteCircular_phaseField_bound
    hγ hγ1 hR hρ hρa hη hηa hηgap g
  apply exists_finiteCircular_phase_continuation_local_forcing hγ hγ1 hR hρ hρa hη hηa hηgap
    hsize hD hH (add_nonneg hB hME) g E hElocal Z hd ?_ hmem htube
  intro t ht
  exact (norm_add_le _ _).trans (add_le_add (hBound (Z t) (htube t ht))
    (hEbound t ⟨ht.1.le, ht.2.le⟩ (Z t) (htube t ht)))

end Euler2D

end
