module

public import RequestProject.Euler.CircularConstrainedDerivative
public import RequestProject.Euler.CircularUnstableComplement

/-! A genuine closed invariant splitting for the actual nonlinear
return map on the original constrained Banach space. -/

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) splitCoordLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) splitCoordLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) splitCoordFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) splitCoordTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) splitCoordTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) splitCoordTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule

def circularConstrainedUnstableCoordinateCLM (γ : ℝ≥0) :
    CircularConstrainedTangentSpace γ →L[ℝ] ℂ :=
  (circularUnstableCoordinateCLM γ).comp (circularConstrainedTangentSubmodule γ).subtypeL

theorem circularConstrainedUnstableCoordinate_embedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (c : ℂ) :
    circularConstrainedUnstableCoordinateCLM γ (circularConstrainedUnstableEmbeddingCLM hγ hγ1 c) = c := by
  change circularUnstableCoordinateCLM γ (circularConstrainedUnstableEmbeddingCLM hγ hγ1 c).val = c
  rw [circularConstrainedUnstableEmbeddingCLM_val, circularUnstableCoordinate_embedding]

def circularConstrainedUnstableProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ :=
  (circularConstrainedUnstableEmbeddingCLM hγ hγ1).comp (circularConstrainedUnstableCoordinateCLM γ)

theorem circularConstrainedUnstableProjectionCLM_val {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (v : CircularConstrainedTangentSpace γ) :
    (circularConstrainedUnstableProjectionCLM hγ hγ1 v).val =
      circularUnstableProjectionCLM hγ hγ1 v.val :=
  circularConstrainedUnstableEmbeddingCLM_val hγ hγ1 _

attribute [local irreducible] circularConstrainedUnstableProjectionCLM

theorem circularConstrainedUnstableProjectionCLM_idempotent {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (v : CircularConstrainedTangentSpace γ) :
    circularConstrainedUnstableProjectionCLM hγ hγ1
      (circularConstrainedUnstableProjectionCLM hγ hγ1 v) =
        circularConstrainedUnstableProjectionCLM hγ hγ1 v := by
  apply Subtype.ext
  simp only [circularConstrainedUnstableProjectionCLM_val]
  exact circularUnstableProjectionCLM_idempotent hγ hγ1 v.val

theorem isCompl_circularConstrainedUnstableProjection_range_ker {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsCompl (circularConstrainedUnstableProjectionCLM hγ hγ1).toLinearMap.range
      (circularConstrainedUnstableProjectionCLM hγ hγ1).ker := by
  have hp : IsIdempotentElem (circularConstrainedUnstableProjectionCLM hγ hγ1).toLinearMap := by
    apply LinearMap.ext
    exact circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1
  exact LinearMap.IsIdempotentElem.isCompl hp

theorem isClosed_circularConstrainedUnstableProjection_range {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsClosed ((circularConstrainedUnstableProjectionCLM hγ hγ1).toLinearMap.range :
      Set (CircularConstrainedTangentSpace γ)) := by
  have he : ((circularConstrainedUnstableProjectionCLM hγ hγ1).toLinearMap.range :
      Set (CircularConstrainedTangentSpace γ)) =
        {v | circularConstrainedUnstableProjectionCLM hγ hγ1 v = v} := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1 w
    · intro hv
      exact ⟨v, hv⟩
  rw [he]
  exact isClosed_eq (circularConstrainedUnstableProjectionCLM hγ hγ1).continuous continuous_id

theorem isClosed_circularConstrainedUnstableProjection_ker {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsClosed ((circularConstrainedUnstableProjectionCLM hγ hγ1).ker :
      Set (CircularConstrainedTangentSpace γ)) :=
  (circularConstrainedUnstableProjectionCLM hγ hγ1).isClosed_ker

theorem circularConstrainedReturnMap_derivative_projection_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i)) :
    (fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0).comp
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) =
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le).comp
        (fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let L := fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let P := circularUnstableProjectionCLM hγ hγ1.le
  have hdv (w : CircularConstrainedTangentSpace γ) : (L w).val = D w.val :=
    circularConstrainedReturnMap_derivative_val hγ hγ1 hρ hX hd hfix harea w
  have hpv (w : CircularConstrainedTangentSpace γ) : (Q w).val = P w.val :=
    circularConstrainedUnstableProjectionCLM_val hγ hγ1.le w
  change (L (Q v)).val = (Q (L v)).val
  calc
    _ = D (Q v).val := hdv (Q v)
    _ = D (P v.val) := congrArg D (hpv v)
    _ = P (D v.val) := congrArg
      (fun A : (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) => A v.val)
      (circularPeriod_derivative_unstableProjection_commute hγ hγ1 hρ hX hd)
    _ = P (L v).val := congrArg P (hdv v).symm
    _ = _ := (hpv (L v)).symm

theorem circularConstrainedReturnMap_derivative_complement_invariant {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {v : CircularConstrainedTangentSpace γ}
    (hv : v ∈ (circularConstrainedUnstableProjectionCLM hγ hγ1.le).ker) :
    fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0 v ∈
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le).ker := by
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let L := fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0
  let P := circularUnstableProjectionCLM hγ hγ1.le
  change circularConstrainedUnstableProjectionCLM hγ hγ1.le v = 0 at hv
  have hraw : P v.val = 0 :=
    (circularConstrainedUnstableProjectionCLM_val hγ hγ1.le v).symm.trans
      (congrArg (fun w : CircularConstrainedTangentSpace γ => w.val) hv)
  have hD : P (D v.val) = 0 :=
    circularPeriod_derivative_unstableComplement_invariant hγ hγ1 hρ hX hd hraw
  change circularConstrainedUnstableProjectionCLM hγ hγ1.le (L v) = 0
  apply Subtype.ext
  calc
    _ = P (L v).val := circularConstrainedUnstableProjectionCLM_val hγ hγ1.le (L v)
    _ = P (D v.val) := congrArg P
      (circularConstrainedReturnMap_derivative_val hγ hγ1 hρ hX hd hfix harea v)
    _ = 0 := hD

end Euler2D

end
