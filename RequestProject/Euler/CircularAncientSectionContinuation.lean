module

public import RequestProject.Euler.GlobalPlanarEulerRestart
public import RequestProject.Euler.CircularPhaseGlobalFlowAgreement
public import RequestProject.Euler.CircularMaterialTransferProfile

/-! A genuine positive-time Euler reference starting at any fixed
negative canonical section follows the same ancient arc to time zero
and then the same original positive continuation. Its fourth moment
is the literal time translate of the original profile. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule

local instance ancientSectionReal_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := (smul_smul a b Z).symm

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_ancient_section_global_continuation {s : ℝ} (hs : s ≤ 0) :
    ∃ Q : GlobalPlanarEulerParticleSystem (circularPhasePatchPlanarVorticity (P.ancient s)),
      (∀ τ ∈ Icc (0 : ℝ) (-s),
        Q.vorticity τ = circularPhasePatchPlanarVorticity (P.ancient (s + τ))) ∧
      (∀ τ : ℝ, 0 ≤ τ → 0 ≤ s + τ →
        Q.vorticity τ = P.positive.vorticity (s + τ)) ∧
      ∀ τ : ℝ, 0 ≤ τ → planarFourthMoment (Q.vorticity τ) = P.moment (s + τ) := by
  let Z := fun τ : ℝ => P.ancient (s + τ)
  have htime (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (-s)) : s + τ ≤ 0 := by
    linarith only [hτ.2]
  have hZc : ContinuousOn Z (Icc (0 : ℝ) (-s)) :=
    P.ancient_continuous.comp (continuous_const.add continuous_id).continuousOn htime
  have hZm (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (-s)) :
      Z τ ∈ circularQuarterPhaseDomain hγ hγ1 := P.ancient_domain (s + τ) (htime τ hτ)
  have hZd (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (-s)) :
      HasDerivAt Z (circularBanachField hγ hγ1 (Z τ)) τ := by
    have hh := (P.ancient_derivative (s + τ) (htime τ hτ)).scomp τ
      ((hasDerivAt_id τ).const_add s)
    simp only [Function.comp_def, one_smul] at hh
    change HasDerivAt (fun u : ℝ => P.ancient (s + u))
      (circularBanachField hγ hγ1 (P.ancient (s + τ))) τ
    exact hh
  have hZ0 : Z 0 = P.ancient s := by simp only [Z, add_zero]
  obtain ⟨Q⟩ := exists_circularPhasePatch_globalPlanarEuler hγ hγ1 (P.ancient_domain s hs)
  have hagreement := exists_circularPhase_globalEuler_material_agreement hγ hγ1 Z
    (neg_nonneg.mpr hs) hZc hZm hZd
  rw [hZ0] at hagreement
  obtain ⟨_F, _hFc, _hFic, _hF0, _hFarea, _hFQ, hden, _hvel⟩ := hagreement Q
  have hnegative (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (-s)) :
      Q.vorticity τ = circularPhasePatchPlanarVorticity (P.ancient (s + τ)) :=
    funext (hden τ hτ)
  have hzero : Q.vorticity (-s) = circularPhasePatchPlanarVorticity (P.ancient 0) := by
    simpa only [add_neg_cancel] using hnegative (-s) ⟨neg_nonneg.mpr hs, le_rfl⟩
  have hpositive (τ : ℝ) (_hτ : 0 ≤ τ) (hpos : 0 ≤ s + τ) :
      Q.vorticity τ = P.positive.vorticity (s + τ) := by
    funext x
    have hh := Q.vorticity_add_eq_of_atTime_eq (neg_nonneg.mpr hs) P.positive
      (integrable_circularPhasePatchPlanarVorticity hγ hγ1 (P.ancient_domain 0 le_rfl))
      (norm_circularPhasePatchPlanarVorticity_le hγ hγ1 (P.ancient_domain 0 le_rfl))
      hzero hpos x
    simpa only [neg_add_cancel_left] using hh
  refine ⟨Q, hnegative, hpositive, ?_⟩
  intro τ hτ
  by_cases hneg : s + τ ≤ 0
  · have hτend : τ ≤ -s := by linarith only [hneg]
    rw [hnegative τ ⟨hτ, hτend⟩, P.moment_negative (s + τ) hneg]
    exact planarFourthMoment_circularPhasePatchPlanarVorticity hγ hγ1
      (P.ancient_domain (s + τ) hneg)
  · have hpos : 0 ≤ s + τ := (lt_of_not_ge hneg).le
    rw [hpositive τ hτ hpos, P.moment_positive (s + τ) hpos]

end CircularMaterialTransferProfile
end Euler2D

end
