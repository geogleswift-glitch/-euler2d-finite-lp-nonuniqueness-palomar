module

public import RequestProject.Euler.CircularConstrainedReturnMap
public import RequestProject.Euler.CircularPeriodRotationCovariance

/-! The original weighted physical rotation acts isometrically on the
same fourfold fixed-area tangent space. The original chart and actual
return map are equivariant on one neighborhood before choosing angle. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) constrainedRotationLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) constrainedRotationLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) constrainedRotationFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) constrainedRotationTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) constrainedRotationTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)

theorem littleContourArea_rotation {γ : ℝ≥0} (b : ℝ) (Z : LittleContourSpace γ) :
    littleContourArea γ (contourRotationLittleCLM γ b Z) = littleContourArea γ Z := by
  change loopArea (LittleContourSpace.lift γ (contourRotationLittleCLM γ b Z)) =
    loopArea (LittleContourSpace.lift γ Z)
  rw [lift_contourRotationLittleCLM]
  exact loopArea_rotShift b (ContourC1Space.contDiff_lift Z.val) (LittleContourSpace.periodic_lift Z)

theorem littleContourEllCLM_rotation {γ : ℝ≥0} (r b : ℝ) (Z : LittleContourSpace γ) :
    littleContourEllCLM γ r (contourRotationLittleCLM γ b Z) = littleContourEllCLM γ r Z := by
  simp only [littleContourEllCLM_eq_ellFun, lift_contourRotationLittleCLM]
  exact ellFun_rotShift r b (LittleContourSpace.periodic_lift Z)

theorem contourRotationLittleCLM_mem_fourfold {γ : ℝ≥0} (b : ℝ) (Z : LittleContourSpace γ)
    (hZ : Z ∈ fourfoldLittleContourSubmodule γ) :
    contourRotationLittleCLM γ b Z ∈ fourfoldLittleContourSubmodule γ := by
  have hz : contourRotationLittleCLM γ (Real.pi / 2) Z = Z := by
    change contourRotationLittleCLM γ (Real.pi / 2) Z - Z = 0 at hZ
    exact sub_eq_zero.mp hZ
  change contourRotationLittleCLM γ (Real.pi / 2) (contourRotationLittleCLM γ b Z) -
    contourRotationLittleCLM γ b Z = 0
  rw [contourRotationLittleCLM_add, add_comm (Real.pi / 2) b,
    ← contourRotationLittleCLM_add, hz, sub_self]

theorem contourRotationLittleCLM_reference {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (r b : ℝ) :
    contourRotationLittleCLM γ b (littleReferenceCircle hγ hγ1 r) = littleReferenceCircle hγ hγ1 r := by
  apply Subtype.ext
  exact contourRotationC1_refCircle b _ (lift_littleReferenceCircle hγ hγ1 r)

theorem littleAreaChart_rotation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (r b : ℝ) (Z : LittleContourSpace γ) :
    littleAreaChart hγ hγ1 r (contourRotationLittleCLM γ b Z) =
      contourRotationLittleCLM γ b (littleAreaChart hγ hγ1 r Z) := by
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (littleAreaChart hγ hγ1 r (contourRotationLittleCLM γ b Z)) θ =
    LittleContourSpace.lift γ (contourRotationLittleCLM γ b (littleAreaChart hγ hγ1 r Z)) θ
  simp only [lift_littleAreaChart, lift_contourRotationLittleCLM]
  exact congrFun (areaChart_equivariant r b (ContourC1Space.contDiff_lift Z.val)
    (LittleContourSpace.periodic_lift Z)) θ

theorem littleFourfoldProjectionCLM_rotation {γ : ℝ≥0} (b : ℝ) (Z : LittleContourSpace γ) :
    littleFourfoldProjectionCLM γ (contourRotationLittleCLM γ b Z) =
      contourRotationLittleCLM γ b (littleFourfoldProjectionCLM γ Z) := by
  let R := contourRotationLittleCLM γ b
  let Q := contourRotationLittleCLM γ (Real.pi / 2)
  have hc (u : LittleContourSpace γ) : Q (R u) = R (Q u) := by
    dsimp only [Q, R]
    rw [contourRotationLittleCLM_add, contourRotationLittleCLM_add, add_comm]
  change (1 / 4 : ℝ) • (R Z + Q (R Z) + Q (Q (R Z)) + Q (Q (Q (R Z)))) =
    R ((1 / 4 : ℝ) • (Z + Q Z + Q (Q Z) + Q (Q (Q Z))))
  simp only [hc, map_smul, map_add]

theorem littleAreaTangentProjection_rotation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (r b : ℝ) (Z : LittleContourSpace γ) :
    littleAreaTangentProjection hγ hγ1 r (contourRotationLittleCLM γ b Z) =
      contourRotationLittleCLM γ b (littleAreaTangentProjection hγ hγ1 r Z) := by
  simp only [littleAreaTangentProjection_apply, littleContourEllCLM_rotation, map_sub, map_smul,
    contourRotationLittleCLM_reference]

theorem circularConstraintProjectionCLM_rotation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (b : ℝ) (Z : Fin 2 → LittleContourSpace γ) :
    circularConstraintProjectionCLM hγ hγ1 (contourRotationFamilyLittleCLM γ b Z) =
      contourRotationFamilyLittleCLM γ b (circularConstraintProjectionCLM hγ hγ1 Z) := by
  funext i
  change littleAreaTangentProjection hγ hγ1 (circularContourRadii i)
      (littleFourfoldProjectionCLM γ (contourRotationLittleCLM γ b (Z i))) =
    contourRotationLittleCLM γ b
      (littleAreaTangentProjection hγ hγ1 (circularContourRadii i) (littleFourfoldProjectionCLM γ (Z i)))
  rw [littleFourfoldProjectionCLM_rotation, littleAreaTangentProjection_rotation]

theorem contourRotationFamily_mem_constrainedTangent {γ : ℝ≥0} (b : ℝ)
    (v : CircularConstrainedTangentSpace γ) :
    contourRotationFamilyLittleCLM γ b v.val ∈ circularConstrainedTangentSubmodule γ := by
  intro i
  refine ⟨contourRotationLittleCLM_mem_fourfold b (v.val i) (v.property i).1, ?_⟩
  change littleContourEllCLM γ (circularContourRadii i) (contourRotationLittleCLM γ b (v.val i)) = 0
  rw [littleContourEllCLM_rotation]
  exact (v.property i).2

def circularConstrainedRotationCLM (γ : ℝ≥0) (b : ℝ) :
    CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ :=
  ((contourRotationFamilyLittleCLM γ b).comp (circularConstrainedTangentSubmodule γ).subtypeL).codRestrict
    (circularConstrainedTangentSubmodule γ) (contourRotationFamily_mem_constrainedTangent b)

theorem circularConstrainedRotationCLM_val {γ : ℝ≥0} (b : ℝ) (v : CircularConstrainedTangentSpace γ) :
    (circularConstrainedRotationCLM γ b v).val = contourRotationFamilyLittleCLM γ b v.val := rfl

theorem norm_circularConstrainedRotationCLM {γ : ℝ≥0} (b : ℝ) (v : CircularConstrainedTangentSpace γ) :
    ‖circularConstrainedRotationCLM γ b v‖ = ‖v‖ := by
  change ‖contourRotationFamilyLittleCLM γ b v.val‖ = ‖v.val‖
  exact norm_contourRotationFamilyLittleCLM b v.val

theorem circularConstrainedChart_rotation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (b : ℝ) (v : CircularConstrainedTangentSpace γ) :
    circularConstrainedChart hγ hγ1 (circularConstrainedRotationCLM γ b v) =
      contourRotationFamilyLittleCLM γ b (circularConstrainedChart hγ hγ1 v) := by
  funext i
  exact littleAreaChart_rotation hγ hγ1.le (circularContourRadii i) b (v.val i)

theorem circularConstraintProjectionToTangentCLM_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (b : ℝ) (Z : Fin 2 → LittleContourSpace γ) :
    circularConstraintProjectionToTangentCLM hγ hγ1 (contourRotationFamilyLittleCLM γ b Z) =
      circularConstrainedRotationCLM γ b (circularConstraintProjectionToTangentCLM hγ hγ1 Z) := by
  apply Subtype.ext
  exact circularConstraintProjectionCLM_rotation hγ hγ1 b Z

theorem circularConstrainedReturnMap_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ}
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (b : ℝ) (v : CircularConstrainedTangentSpace γ)
    (hv : circularConstrainedChart hγ hγ1 v ∈ ball (littleCircularReference hγ hγ1) R) :
    circularConstrainedReturnMap hγ hγ1 (fun W => X W period) (circularConstrainedRotationCLM γ b v) =
      circularConstrainedRotationCLM γ b (circularConstrainedReturnMap hγ hγ1 (fun W => X W period) v) := by
  have hp : period ∈ Icc (0 : ℝ) period := ⟨by unfold period; positivity, le_rfl⟩
  unfold circularConstrainedReturnMap
  rw [circularConstrainedChart_rotation]
  dsimp only
  rw [circularBanachFlow_rotation hγ hγ1 hX b hv hp]
  have hs : contourRotationFamilyLittleCLM γ b (X (circularConstrainedChart hγ hγ1 v) period) -
      littleCircularReference hγ hγ1 =
      contourRotationFamilyLittleCLM γ b (X (circularConstrainedChart hγ hγ1 v) period - littleCircularReference hγ hγ1) := by
    rw [map_sub, contourRotationFamilyLittleCLM_reference]
  rw [hs, circularConstraintProjectionToTangentCLM_rotation]

theorem exists_circularConstrainedReturnMap_rotation_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X) :
    ∃ δ > 0, ∀ b : ℝ, ∀ v : CircularConstrainedTangentSpace γ, ‖v‖ < δ →
      circularConstrainedReturnMap hγ hγ1 (fun W => X W period) (circularConstrainedRotationCLM γ b v) =
        circularConstrainedRotationCLM γ b (circularConstrainedReturnMap hγ hγ1 (fun W => X W period) v) := by
  have hc := (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
  have hnear : ∀ᶠ v in 𝓝 (0 : CircularConstrainedTangentSpace γ),
      circularConstrainedChart hγ hγ1 v ∈ ball (littleCircularReference hγ hγ1) R := by
    apply hc.eventually
    rw [circularConstrainedChart_zero]
    exact isOpen_ball.mem_nhds (mem_ball_self hR)
  obtain ⟨δ, hδ, hδspec⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro b v hv
  exact circularConstrainedReturnMap_rotation hγ hγ1 hX b v
    (hδspec (by simpa only [dist_zero_right] using hv))

end Euler2D

end
