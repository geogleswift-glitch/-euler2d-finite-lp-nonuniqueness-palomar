module

public import RequestProject.Euler.CircularBackwardGraphRotationInvariance
public import RequestProject.Euler.CircularConstrainedSplitting
public import RequestProject.Euler.CircularFourierRotationProjection
public import RequestProject.Euler.ContourCircularRotationDerivative

/-! Exact rotation of the original growing coordinate and embedding.
The same original unstable projection commutes with physical rotation,
so the already fixed backward graph has its literal rotated base. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

attribute [local instance 2000] constrainedRotationLittle_group constrainedRotationLittle_space
  constrainedRotationFamily_tower constrainedRotationTangent_group constrainedRotationTangent_space

theorem contourRotationLittleCLM_fourier_mode {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (n : ℤ) (a : ℂ) (b : ℝ) :
    contourRotationLittleCLM γ b (littleContourFourierMode hγ hγ1 n a) =
      littleContourFourierMode hγ hγ1 n (a * contourCircleCharacter (1 - n) b) := by
  apply Subtype.ext
  exact contourRotationC1_fourier_mode hγ hγ1 n a b

theorem littleContourFourthNormalCoefficientCLM_rotation {γ : ℝ≥0}
    (r b : ℝ) (H : LittleContourSpace γ) :
    littleContourFourthNormalCoefficientCLM γ r (contourRotationLittleCLM γ b H) =
      contourCircleCharacter (-4) b * littleContourFourthNormalCoefficientCLM γ r H := by
  rw [littleContourFourthNormalCoefficientCLM_apply, littleContourFourthNormalCoefficientCLM_apply,
    littleContourFourierCoefficient_rotation, littleContourFourierCoefficient_rotation]
  change (contourCircleCharacter (-4) b * littleContourFourierCoefficient γ 5 H +
      conj (contourCircleCharacter 4 b * littleContourFourierCoefficient γ (-3) H)) / (r : ℂ) = _
  simp only [map_mul, conj_contourCircleCharacter]
  ring

theorem circularFourthNormalCoefficientCLM_rotation {γ : ℝ≥0}
    (b : ℝ) (H : Fin 2 → LittleContourSpace γ) :
    circularFourthNormalCoefficientCLM γ (contourRotationFamilyLittleCLM γ b H) =
      contourCircleCharacter (-4) b • circularFourthNormalCoefficientCLM γ H := by
  funext i
  change littleContourFourthNormalCoefficientCLM γ (circularContourRadii i)
      (contourRotationLittleCLM γ b (H i)) =
    contourCircleCharacter (-4) b * littleContourFourthNormalCoefficientCLM γ (circularContourRadii i) (H i)
  exact littleContourFourthNormalCoefficientCLM_rotation _ b (H i)

theorem circularUnstableCoordinateCLM_rotation {γ : ℝ≥0}
    (b : ℝ) (H : Fin 2 → LittleContourSpace γ) :
    circularUnstableCoordinateCLM γ (contourRotationFamilyLittleCLM γ b H) =
      contourCircleCharacter (-4) b * circularUnstableCoordinateCLM γ H := by
  simp only [circularUnstableCoordinateCLM, ContinuousLinearMap.comp_apply,
    circularFourthNormalCoefficientCLM_rotation, circularEllPlusCLM_apply, ellPlus_complex_smul]

theorem circularUnstableEmbeddingCLM_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (b : ℝ) (c : ℂ) :
    contourRotationFamilyLittleCLM γ b (circularUnstableEmbeddingCLM hγ hγ1 c) =
      circularUnstableEmbeddingCLM hγ hγ1 (contourCircleCharacter (-4) b * c) := by
  funext i
  change contourRotationLittleCLM γ b
      (littleContourFourierModeCLM hγ hγ1 5
        (circularNormalModePlus (circularContourRadii i) (vPlus i) (circularGrowingTangent i) * c) +
      littleContourFourierModeCLM hγ hγ1 (-3)
        (circularNormalModeMinus (circularContourRadii i) (vPlus i) (circularGrowingTangent i) * conj c)) =
    littleContourFourierModeCLM hγ hγ1 5
      (circularNormalModePlus (circularContourRadii i) (vPlus i) (circularGrowingTangent i) *
        (contourCircleCharacter (-4) b * c)) +
    littleContourFourierModeCLM hγ hγ1 (-3)
      (circularNormalModeMinus (circularContourRadii i) (vPlus i) (circularGrowingTangent i) *
        conj (contourCircleCharacter (-4) b * c))
  rw [map_add]
  simp only [littleContourFourierModeCLM_apply]
  rw [contourRotationLittleCLM_fourier_mode, contourRotationLittleCLM_fourier_mode]
  apply congrArg₂ (fun Z W : LittleContourSpace γ => Z + W)
  · congr 1
    ring
  · congr 1
    simp only [map_mul, conj_contourCircleCharacter, neg_neg]
    ring

theorem circularUnstableProjectionCLM_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (b : ℝ) (H : Fin 2 → LittleContourSpace γ) :
    circularUnstableProjectionCLM hγ hγ1 (contourRotationFamilyLittleCLM γ b H) =
      contourRotationFamilyLittleCLM γ b (circularUnstableProjectionCLM hγ hγ1 H) := by
  rw [circularUnstableProjectionCLM_apply, circularUnstableProjectionCLM_apply,
    circularUnstableCoordinateCLM_rotation, circularUnstableEmbeddingCLM_rotation]

theorem circularConstrainedUnstableCoordinateCLM_rotation {γ : ℝ≥0}
    (b : ℝ) (v : CircularConstrainedTangentSpace γ) :
    circularConstrainedUnstableCoordinateCLM γ (circularConstrainedRotationCLM γ b v) =
      contourCircleCharacter (-4) b * circularConstrainedUnstableCoordinateCLM γ v := by
  change circularUnstableCoordinateCLM γ (circularConstrainedRotationCLM γ b v).val =
    contourCircleCharacter (-4) b * circularUnstableCoordinateCLM γ v.val
  rw [circularConstrainedRotationCLM_val]
  exact circularUnstableCoordinateCLM_rotation b v.val

theorem circularConstrainedUnstableEmbeddingCLM_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (b : ℝ) (c : ℂ) :
    circularConstrainedRotationCLM γ b (circularConstrainedUnstableEmbeddingCLM hγ hγ1 c) =
      circularConstrainedUnstableEmbeddingCLM hγ hγ1 (contourCircleCharacter (-4) b * c) := by
  apply Subtype.ext
  rw [circularConstrainedRotationCLM_val, circularConstrainedUnstableEmbeddingCLM_val,
    circularConstrainedUnstableEmbeddingCLM_val]
  exact circularUnstableEmbeddingCLM_rotation hγ hγ1 b c

theorem circularConstrainedUnstableProjectionCLM_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (b : ℝ) (v : CircularConstrainedTangentSpace γ) :
    circularConstrainedUnstableProjectionCLM hγ hγ1 (circularConstrainedRotationCLM γ b v) =
      circularConstrainedRotationCLM γ b (circularConstrainedUnstableProjectionCLM hγ hγ1 v) := by
  apply Subtype.ext
  rw [circularConstrainedUnstableProjectionCLM_val, circularConstrainedRotationCLM_val,
    circularConstrainedRotationCLM_val, circularConstrainedUnstableProjectionCLM_val]
  exact circularUnstableProjectionCLM_rotation hγ hγ1 b v.val

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularConstrainedRotationCLM circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularBanachField circularBanachDomain littleCircularReference contourC1GraphSubmodule holderGraphSubmodule

theorem exists_same_circularBackwardGraph_exact_rotation_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    {w r : ℝ} (hw : 1 ≤ w) (hr : 0 < r)
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) w r x) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ (b : ℝ) (ξ : CircularConstrainedTangentSpace γ),
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
      x (circularConstrainedRotationCLM γ b ξ) =
        (fun n => circularConstrainedRotationCLM γ b (x ξ n)) := by
  obtain ⟨η, hη, hηr, hinv⟩ := exists_circularConstrained_backwardGraph_rotation_radius
    hγ hγ1 hR hX hd hfix hw hr hg
  refine ⟨η, hη, hηr, ?_⟩
  intro b ξ hξ hξη
  have hbase : circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstrainedRotationCLM γ b (x ξ 0)) = circularConstrainedRotationCLM γ b ξ := by
    have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
    change circularConstrainedUnstableProjectionCLM hγ hγle
      (circularConstrainedRotationCLM γ b (x ξ 0)) = circularConstrainedRotationCLM γ b ξ
    rw [circularConstrainedUnstableProjectionCLM_rotation hγ hγle b (x ξ 0)]
    exact congrArg (circularConstrainedRotationCLM γ b) (hg.coordinate ξ hξ (hξη.trans hηr))
  have he := (hinv b ξ hξ hξη).2
  rw [hbase] at he
  exact he

end Euler2D

end
