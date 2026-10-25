module

public import RequestProject.Euler.CircularConstrainedReturnMap
public import RequestProject.Euler.BanachQuadraticRemainder


/-! The actual strength-weighted fourth patch moment restricted to
the original fourfold fixed-area tangent coordinates. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) quadraticChartLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) quadraticChartLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) quadraticChartFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) quadraticChartTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) quadraticChartTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) quadraticChartTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule

theorem exists_circularConstrainedChart_quadratic_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ C > 0, ∃ r > 0, ∀ v ∈ closedBall (0 : CircularConstrainedTangentSpace γ) r,
      ‖circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1 - v.val‖ ≤ C * ‖v‖ ^ 2 ∧
      ‖circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1‖ ≤ (1 + C * r) * ‖v‖ := by
  let f : CircularConstrainedTangentSpace γ → Fin 2 → LittleContourSpace γ :=
    fun v => circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1
  have hf : ContDiffAt ℝ 2 f 0 :=
    (contDiffAt_circularConstrainedChart hγ hγ1 2 0 (fun i => by
      change 0 < 1 - littleContourArea γ 0 / _
      simp only [littleContourArea_zero, zero_div, sub_zero, zero_lt_one])).sub contDiffAt_const
  have hf0 : f 0 = 0 := by dsimp only [f]; rw [circularConstrainedChart_zero, sub_self]
  have hd : fderiv ℝ f 0 = (circularConstrainedTangentSubmodule γ).subtypeL :=
    ((hasFDerivAt_circularConstrainedChart_zero hγ hγ1).sub_const
      (littleCircularReference hγ hγ1)).fderiv
  obtain ⟨C, hC, r, hr, hquad⟩ := exists_banachLocalRemainder_quadratic_bound hf hf0
  refine ⟨C, hC, r, hr, ?_⟩
  intro v hv
  have hq := hquad v hv
  change ‖f v - fderiv ℝ f 0 v‖ ≤ C * ‖v‖ ^ 2 at hq
  rw [hd] at hq
  have hq' : ‖circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1 - v.val‖ ≤ C * ‖v‖ ^ 2 := hq
  have hvnorm : ‖v‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hv
  refine ⟨hq', ?_⟩
  calc
    _ ≤ ‖circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1 - v.val‖ + ‖v.val‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ C * ‖v‖ ^ 2 + ‖v‖ := add_le_add hq' le_rfl
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left hvnorm (mul_nonneg hC.le (norm_nonneg v))
      nlinarith

end Euler2D

end
