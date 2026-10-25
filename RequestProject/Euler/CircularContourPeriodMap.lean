module

public import RequestProject.Euler.CircularBanachDynamics
public import RequestProject.Euler.BanachReferenceContinuation

/-! An actual full-period material contour flow near the circular
reference, with every requested finite initial-data order. In particular
this constructs a genuine C³ return map of the original boundary ODE. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) circularPeriodC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularPeriodLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularPeriodLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularBanachField {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ :=
  finiteContourPhaseFieldTotal hγ hγ1 (circularReferenceC1 hγ hγ1) circularContourRadii
    (fun i => by fin_cases i <;> simp [circularContourRadii, cellA_pos])
    (lift_circularReferenceC1 hγ hγ1) circularContourStrengths

def circularBanachDomain {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    Set (Fin 2 → LittleContourSpace γ) :=
  {Z | IsPhaseAdmissibleLittleContourFamily (circularReferenceC1 hγ hγ1) circularContourRadii Z}

theorem littleCircularMaterialContours_zero {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    littleCircularMaterialContours hγ hγ1 0 = littleCircularReference hγ hγ1 := by
  funext i
  simp only [littleCircularMaterialContours, mul_zero, Real.cos_zero, one_smul,
    Real.sin_zero, zero_smul, add_zero]

set_option maxHeartbeats 600000 in
theorem exists_circularContour_period_flow {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (n : ℕ) :
    ∃ ρ > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) ρ) period X ∧
      (∀ t ∈ Icc 0 period, ContDiffOn ℝ n (fun W => X W t)
        (ball (littleCircularReference hγ hγ1) ρ)) ∧
      X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
      ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ t ∈ Icc 0 period, ∀ i θ,
        HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
          (contourBoundaryField circularContourStrengths
            (fun j => LittleContourSpace.lift γ (X W t j)) i θ) t := by
  have hU : IsOpen (circularBanachDomain hγ hγ1) :=
    isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ ∞ (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) :=
    contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (⊤ : ℕ∞)
  have hcd (t : ℝ) : HasDerivAt (littleCircularMaterialContours hγ hγ1)
      (circularBanachField hγ hγ1 (littleCircularMaterialContours hγ hγ1 t)) t :=
    littleCircularMaterialContours_hasDerivAt hγ hγ1 t
  have hp : 0 < period := by unfold period; positivity
  obtain ⟨ρ, hρ, X, hX, hs, he⟩ := exists_smooth_banachFlow_along_reference n hU hf
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous
    (phaseAdmissible_littleCircularMaterialContours hγ hγ1) hcd hp
  rw [littleCircularMaterialContours_zero] at hX hs he
  refine ⟨ρ, hρ, X, hX, hs, ?_, ?_⟩
  · calc
      X (littleCircularReference hγ hγ1) period = littleCircularMaterialContours hγ hγ1 period :=
        he ⟨hp.le, le_rfl⟩
      _ = littleCircularReference hγ hγ1 := by
        rw [littleCircularMaterialContours_period, littleCircularMaterialContours_zero]
  · intro W hW t ht i θ
    have hd := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
      (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t (hX.hasDerivAt W hW t ht)
    change HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
      (LittleContourSpace.lift γ (circularBanachField hγ hγ1 (X W t) i) θ) t at hd
    rw [circularBanachField, lift_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _
      (X W t) (hX.mem W hW t ht)] at hd
    exact hd

theorem exists_circularContour_C3_periodMap {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ ρ > 0, ∃ P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ,
      ContDiffOn ℝ 3 P (ball (littleCircularReference hγ hγ1) ρ) ∧
      P (littleCircularReference hγ hγ1) = littleCircularReference hγ hγ1 ∧
      ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ,
        ∃ Z : ℝ → Fin 2 → LittleContourSpace γ,
          Z 0 = W ∧ Z period = P W ∧
          (∀ t ∈ Icc 0 period, Z t ∈ circularBanachDomain hγ hγ1) ∧
          ∀ t ∈ Icc 0 period, ∀ i θ,
            HasDerivAt (fun s => LittleContourSpace.lift γ (Z s i) θ)
              (contourBoundaryField circularContourStrengths
                (fun j => LittleContourSpace.lift γ (Z t j)) i θ) t := by
  obtain ⟨ρ, hρ, X, hX, hs, hfix, hmat⟩ := exists_circularContour_period_flow hγ hγ1 3
  have hp : 0 ≤ period := by unfold period; positivity
  refine ⟨ρ, hρ, fun W => X W period, hs period ⟨hp, le_rfl⟩, hfix, ?_⟩
  intro W hW
  exact ⟨X W, hX.initial W hW, rfl, hX.mem W hW, hmat W hW⟩

end Euler2D

end
