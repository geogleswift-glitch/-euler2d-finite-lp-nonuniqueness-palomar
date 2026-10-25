module

public import RequestProject.Euler.CircularConstrainedChart
public import RequestProject.Euler.CircularConstraintProjection
public import RequestProject.Euler.CircularUnstableProjection

/-! Actual nonlinear return coordinates on the original complete
fourfold fixed-area tangent space. Local conjugacy to the material flow
requires the actual fixed-area inverse-chart neighborhood. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) returnCoordLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) returnCoordLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) returnCoordFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) returnCoordTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) returnCoordTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) returnCoordTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

def circularConstraintProjectionToTangentCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] CircularConstrainedTangentSpace γ :=
  (circularConstraintProjectionCLM hγ hγ1).codRestrict (circularConstrainedTangentSubmodule γ)
    (fun Z i => circularConstraintProjectionCLM_mem hγ hγ1 Z i)

theorem circularConstraintProjectionToTangentCLM_val {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (Z : Fin 2 → LittleContourSpace γ) :
    (circularConstraintProjectionToTangentCLM hγ hγ1 Z).val =
      circularConstraintProjectionCLM hγ hγ1 Z := rfl

theorem circularConstrainedTangent_coe_smul {γ : ℝ≥0} (a : ℝ)
    (v : CircularConstrainedTangentSpace γ) : (a • v).val = a • v.val := rfl

def circularConstrainedReturnMap {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ)
    (v : CircularConstrainedTangentSpace γ) : CircularConstrainedTangentSpace γ :=
  circularConstraintProjectionToTangentCLM hγ hγ1.le
    (P (circularConstrainedChart hγ hγ1 v) - littleCircularReference hγ hγ1)

theorem circularConstrainedReturnMap_zero {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ)
    (hP : P (littleCircularReference hγ hγ1) = littleCircularReference hγ hγ1) :
    circularConstrainedReturnMap hγ hγ1 P 0 = 0 := by
  unfold circularConstrainedReturnMap
  rw [circularConstrainedChart_zero, hP, sub_self, map_zero]

theorem hasFDerivAt_circularConstrainedChart_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    HasFDerivAt (circularConstrainedChart hγ hγ1)
      (circularConstrainedTangentSubmodule γ).subtypeL 0 := by
  apply hasFDerivAt_pi''
  intro i
  have hi : HasFDerivAt (fun v : CircularConstrainedTangentSpace γ => v.val i)
      ((ContinuousLinearMap.proj i).comp (circularConstrainedTangentSubmodule γ).subtypeL) 0 :=
    ((ContinuousLinearMap.proj i).comp (circularConstrainedTangentSubmodule γ).subtypeL).hasFDerivAt
  have h := (hasFDerivAt_littleAreaChart_zero hγ hγ1.le (circularContourRadii i)).comp
    (0 : CircularConstrainedTangentSpace γ) hi
  simpa only [Function.comp_def, ContinuousLinearMap.id_comp] using h

theorem contDiffAt_circularConstrainedReturnMap {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (n : ℕ∞)
    {P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ}
    (hP : ContDiffAt ℝ n P (littleCircularReference hγ hγ1)) :
    ContDiffAt ℝ n (circularConstrainedReturnMap hγ hγ1 P) 0 := by
  have hchart : ContDiffAt ℝ n (circularConstrainedChart hγ hγ1) 0 :=
    contDiffAt_circularConstrainedChart hγ hγ1 n 0 (fun i => by
      change 0 < 1 - littleContourArea γ 0 / _
      simp only [littleContourArea_zero, zero_div, sub_zero, zero_lt_one])
  have hP' : ContDiffAt ℝ n P (circularConstrainedChart hγ hγ1 0) := by
    rw [circularConstrainedChart_zero]
    exact hP
  exact (circularConstraintProjectionToTangentCLM hγ hγ1.le).contDiff.contDiffAt.comp 0
    ((hP'.comp 0 hchart).sub contDiffAt_const)

theorem hasFDerivAt_circularConstrainedReturnMap_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ}
    (hP : DifferentiableAt ℝ P (littleCircularReference hγ hγ1)) :
    HasFDerivAt (circularConstrainedReturnMap hγ hγ1 P)
      ((circularConstraintProjectionToTangentCLM hγ hγ1.le).comp
        ((fderiv ℝ P (littleCircularReference hγ hγ1)).comp
          (circularConstrainedTangentSubmodule γ).subtypeL)) 0 := by
  have hP' : HasFDerivAt P (fderiv ℝ P (littleCircularReference hγ hγ1))
      (circularConstrainedChart hγ hγ1 0) := by
    rw [circularConstrainedChart_zero]
    exact hP.hasFDerivAt
  exact (circularConstraintProjectionToTangentCLM hγ hγ1.le).hasFDerivAt.comp 0
    ((hP'.comp 0 (hasFDerivAt_circularConstrainedChart_zero hγ hγ1)).sub_const
      (littleCircularReference hγ hγ1))

def circularConstrainedUnstableEmbeddingCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ℂ →L[ℝ] CircularConstrainedTangentSpace γ :=
  (circularConstraintProjectionToTangentCLM hγ hγ1).comp (circularUnstableEmbeddingCLM hγ hγ1)

theorem circularConstrainedUnstableEmbeddingCLM_val {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (c : ℂ) :
    (circularConstrainedUnstableEmbeddingCLM hγ hγ1 c).val = circularUnstableEmbeddingCLM hγ hγ1 c := by
  apply circularConstraintProjectionCLM_of_mem hγ hγ1
  intro i
  exact circularUnstableSpace_mem_fourfold_area hγ hγ1 ⟨c, rfl⟩ i

theorem circularConstrainedReturnMap_derivative_unstable_val {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) (c : ℂ) :
    (fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c)).val =
        (-lamMult : ℝ) • circularUnstableEmbeddingCLM hγ hγ1.le c := by
  rw [(hasFDerivAt_circularConstrainedReturnMap_zero hγ hγ1 hd).fderiv]
  change circularConstraintProjectionCLM hγ hγ1.le
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c).val) = _
  have he := circularConstrainedUnstableEmbeddingCLM_val hγ hγ1.le c
  calc
    _ = circularConstraintProjectionCLM hγ hγ1.le
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
          (circularUnstableEmbeddingCLM hγ hγ1.le c)) :=
      congrArg (fun Z : Fin 2 → LittleContourSpace γ =>
        circularConstraintProjectionCLM hγ hγ1.le
          (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) Z)) he
    _ = circularConstraintProjectionCLM hγ hγ1.le
        ((-lamMult : ℝ) • circularUnstableEmbeddingCLM hγ hγ1.le c) :=
      congrArg (circularConstraintProjectionCLM hγ hγ1.le)
        (circularPeriod_derivative_unstableEmbedding hγ hγ1 hρ hX c)
    _ = _ := by
      apply circularConstraintProjectionCLM_of_mem hγ hγ1.le
      intro i
      exact (fourfoldLittleContourSubmodule γ ⊓
        LittleContourAreaConstraint γ (circularContourRadii i)).smul_mem (-lamMult : ℝ)
          (circularUnstableSpace_mem_fourfold_area hγ hγ1.le ⟨c, rfl⟩ i)

theorem circularConstrainedReturnMap_derivative_unstable {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) (c : ℂ) :
    fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c) =
        (-lamMult : ℝ) • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c := by
  have hL := circularConstrainedReturnMap_derivative_unstable_val hγ hγ1 hρ hX hd c
  have hR : ((-lamMult : ℝ) • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c).val =
      (-lamMult : ℝ) • circularUnstableEmbeddingCLM hγ hγ1.le c :=
    (circularConstrainedTangent_coe_smul (-lamMult : ℝ)
      (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c)).trans
        (congrArg (fun Z : Fin 2 → LittleContourSpace γ => (-lamMult : ℝ) • Z)
          (circularConstrainedUnstableEmbeddingCLM_val hγ hγ1.le c))
  exact Subtype.ext (hL.trans hR.symm)

end Euler2D

end
