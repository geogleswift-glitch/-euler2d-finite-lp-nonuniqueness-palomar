module

public import RequestProject.Euler.CircularFinitePhaseFieldBound

/-! A single continuous, uniformly state-Lipschitz forcing gives a
finite bound for the actual whole material velocity on a fixed finite
time interval and on the strict circular phase tube. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) circularForcedBoundLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularForcedBoundLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularForcedBoundC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem exists_finiteCircular_forced_phaseField_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ η a D : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρa : ρ ≤ cellA / 4)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    (ha : 0 < a) (hsize : R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4)
    {N : ℕ} (g : FiniteCircularIndex N → ℝ)
    (E : ℝ → (FiniteCircularIndex N → LittleContourSpace γ) →
      FiniteCircularIndex N → LittleContourSpace γ) {K : ℝ≥0}
    (hELip : ∀ t, LipschitzOnWith K (E t) (ball 0 (a / 4)))
    (hEc : ∀ W ∈ ball 0 (a / 4), Continuous (fun t => E t W)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) D,
      ∀ Z : FiniteCircularIndex N → LittleContourSpace γ,
      (∃ b : FiniteCircularIndex N → ℝ, ∀ p,
        ‖contourParameterShiftC1 (b p) (Z p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1) →
      ‖finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g Z + E t Z‖ ≤ M := by
  obtain ⟨B, hB, hself⟩ :=
    exists_finiteCircular_phaseField_bound hγ hγ1 hR hρ hρa hη hηa hηgap g
  have hzero : (0 : FiniteCircularIndex N → LittleContourSpace γ) ∈ ball 0 (a / 4) :=
    mem_ball_self (by positivity)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hEc 0 hzero).continuousOn
  have hcap : 0 ≤ R * (‖littleCircularReference hγ hγ1‖ + η) := by positivity
  refine ⟨B + ((K : ℝ) * (R * (‖littleCircularReference hγ hγ1‖ + η)) + |C|), by positivity, ?_⟩
  intro t ht Z hZ
  have hρ1 : ρ ≤ 1 := by linarith [cellA_lt_one]
  have hZn : ‖Z‖ ≤ R * (‖littleCircularReference hγ hγ1‖ + η) :=
    norm_finiteCircular_closedPhaseTube_le hγ hγ1 hR hρ hρ1 hη hZ
  have hZball : Z ∈ ball 0 (a / 4) := mem_ball_zero_iff.mpr (hZn.trans_lt hsize)
  have hh := (hELip t).dist_le_mul Z hZball 0 hzero
  simp only [dist_eq_norm, sub_zero] at hh
  have hEnorm : ‖E t Z‖ ≤ (K : ℝ) * (R * (‖littleCircularReference hγ hγ1‖ + η)) + |C| :=
    (norm_le_norm_sub_add (E t Z) (E t 0)).trans
      (add_le_add (hh.trans (mul_le_mul_of_nonneg_left hZn K.2)) ((hC t ht).trans (le_abs_self C)))
  exact (norm_add_le _ _).trans (add_le_add (hself Z hZ) hEnorm)

end Euler2D

end
