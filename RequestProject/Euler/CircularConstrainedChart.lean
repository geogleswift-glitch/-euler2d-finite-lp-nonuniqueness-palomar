module

public import RequestProject.Euler.CircularAreaChartInverse
public import RequestProject.Euler.CircularConstrainedPeriodMap
public import RequestProject.Euler.ClosedSubspaceSmoothness

/-! Actual Banach coordinates for the original fourfold fixed-area
contour manifold. The tangent space is the original closed intersection. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) constrainedChartLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) constrainedChartLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) constrainedChartFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm

def circularConstrainedTangentSubmodule (γ : ℝ≥0) :
    Submodule ℝ (Fin 2 → LittleContourSpace γ) where
  carrier := {v | ∀ i, v i ∈
    fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i)}
  zero_mem' := fun i => (fourfoldLittleContourSubmodule γ ⊓
    LittleContourAreaConstraint γ (circularContourRadii i)).zero_mem
  add_mem' := fun hv hw i => (fourfoldLittleContourSubmodule γ ⊓
    LittleContourAreaConstraint γ (circularContourRadii i)).add_mem (hv i) (hw i)
  smul_mem' := fun a v hv i => (fourfoldLittleContourSubmodule γ ⊓
    LittleContourAreaConstraint γ (circularContourRadii i)).smul_mem a (hv i)

abbrev CircularConstrainedTangentSpace (γ : ℝ≥0) := circularConstrainedTangentSubmodule γ

local instance (priority := 2000) constrainedChartTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) constrainedChartTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)

theorem isClosed_circularConstrainedTangentSubmodule (γ : ℝ≥0) :
    IsClosed (circularConstrainedTangentSubmodule γ : Set (Fin 2 → LittleContourSpace γ)) := by
  change IsClosed {v : Fin 2 → LittleContourSpace γ | ∀ i, v i ∈
    fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i)}
  have hc (i : Fin 2) : IsClosed {v : Fin 2 → LittleContourSpace γ | v i ∈
      fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i)} :=
    ((isClosed_fourfoldLittleContourSubmodule γ).inter
      (isClosed_littleContourAreaConstraint γ (circularContourRadii i))).preimage (continuous_apply i)
  simpa only [setOf_forall] using isClosed_iInter hc

instance circularConstrainedTangentSpace_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) :=
  (isClosed_circularConstrainedTangentSubmodule γ).completeSpace_coe

def circularConstrainedChart {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (v : CircularConstrainedTangentSpace γ) (i : Fin 2) : LittleContourSpace γ :=
  littleAreaChart hγ hγ1.le (circularContourRadii i) (v.val i)

def circularAreaChartInverseFamily {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z : Fin 2 → LittleContourSpace γ) (i : Fin 2) : LittleContourSpace γ :=
  littleAreaChartInverse hγ hγ1.le (circularContourRadii i) (Z i)

theorem circularConstrainedChart_zero {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    circularConstrainedChart hγ hγ1 0 = littleCircularReference hγ hγ1 := by
  funext i
  change littleAreaChart hγ hγ1.le (circularContourRadii i) 0 = _
  exact littleAreaChart_zero hγ (by exact_mod_cast hγ1.le) (circularContourRadii i)

theorem circularConstrainedChart_fourfold {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (v : CircularConstrainedTangentSpace γ) (i : Fin 2) :
    circularConstrainedChart hγ hγ1 v i ∈ fourfoldLittleContourSubmodule γ :=
  littleAreaChart_mem_fourfold hγ hγ1.le _ _ (v.property i).1

theorem circularAreaChartInverseFamily_chart {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (v : CircularConstrainedTangentSpace γ) :
    circularAreaChartInverseFamily hγ hγ1 (circularConstrainedChart hγ hγ1 v) = v.val := by
  funext i
  apply littleAreaChartInverse_littleAreaChart hγ hγ1.le
    (by fin_cases i <;> simp [circularContourRadii, cellA_pos.ne'])
  exact (v.property i).2

theorem circularAreaChartInverseFamily_mem {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (Z : Fin 2 → LittleContourSpace γ)
    (hZ : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) :
    circularAreaChartInverseFamily hγ hγ1 Z ∈ circularConstrainedTangentSubmodule γ := by
  intro i
  exact littleAreaChartInverse_mem_fourfold_area hγ hγ1.le
    (by fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']) (Z i) (hZ i)

theorem contDiffAt_circularAreaChartInverseFamily {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (n : ℕ∞) (Z : Fin 2 → LittleContourSpace γ) :
    ContDiffAt ℝ n (circularAreaChartInverseFamily hγ hγ1) Z := by
  apply contDiffAt_pi.mpr
  intro i
  exact (analyticAt_littleAreaChartInverse hγ hγ1.le (circularContourRadii i) (Z i)).contDiffAt.comp Z
    (ContinuousLinearMap.proj i : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ).contDiff.contDiffAt

theorem contDiffAt_circularConstrainedChart {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (n : ℕ∞) (v : CircularConstrainedTangentSpace γ)
    (hpos : ∀ i, 0 < 1 - littleContourArea γ (v.val i) / (Real.pi * circularContourRadii i ^ 2)) :
    ContDiffAt ℝ n (circularConstrainedChart hγ hγ1) v := by
  apply contDiffAt_pi.mpr
  intro i
  let L : CircularConstrainedTangentSpace γ →L[ℝ] LittleContourSpace γ :=
    (ContinuousLinearMap.proj i).comp (circularConstrainedTangentSubmodule γ).subtypeL
  have hi : ContDiffAt ℝ n (fun w : CircularConstrainedTangentSpace γ => w.val i) v :=
    L.contDiff.contDiffAt
  exact (analyticAt_littleAreaChart hγ hγ1.le _ _ (hpos i)).contDiffAt.comp v hi

theorem circularConstrainedChart_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (v : CircularConstrainedTangentSpace γ)
    (hpos : ∀ i, 0 < 1 - littleContourArea γ (v.val i) / (Real.pi * circularContourRadii i ^ 2))
    (i : Fin 2) :
    littleContourArea γ (circularConstrainedChart hγ hγ1 v i) = Real.pi * circularContourRadii i ^ 2 := by
  have hr : circularContourRadii i ≠ 0 := by
    fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']
  apply loopArea_littleAreaChart hγ hγ1.le hr _ (v.property i).2
  have hrpos : 0 < circularContourRadii i := by fin_cases i <;> simp [circularContourRadii, cellA_pos]
  have hden : 0 < Real.pi * circularContourRadii i ^ 2 := by positivity
  exact ((div_lt_one hden).mp (by linarith [hpos i])).le

end Euler2D

end
