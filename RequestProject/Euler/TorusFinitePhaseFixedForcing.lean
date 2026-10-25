module

public import RequestProject.Euler.TorusForcedFinitePhaseFlow

/-! Expose one fixed actual forcing for the whole provisional interval.
This same Banach-valued field is available at every restart, with its
literal original Euler label-integral lift retained. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) torusFixedPhaseLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) torusFixedPhaseLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_finitePhase_fixed_actual_forcing
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (hmean : (∫ x in torusBox, f x) = 0)
    {ε a : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0)
    {γ : ℝ≥0} {ι : Type} [Fintype ι] (hγ1 : (γ : ℝ) ≤ 1) :
    ∃ K : ℝ≥0, ∃ E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ,
      (∀ t, LipschitzOnWith K (E t) (ball 0 (a / 4))) ∧
      (∀ Z ∈ ball 0 (a / 4), Continuous (fun t => E t Z)) ∧
      (∀ t, ∀ Z : ι → LittleContourSpace γ, ‖Z‖ < a / 4 → ∀ i θ,
        LittleContourSpace.lift γ (E t Z i) θ =
          actualTorusCorrectionVelocity
            (S.physicalComplexSource w (projIcc 0 ε hε.le t)) (LittleContourSpace.lift γ (Z i) θ)) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ Z : ι → LittleContourSpace γ, ‖Z‖ < a / 4 → ∀ i θ,
        LittleContourSpace.lift γ (E t Z i) θ =
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (LittleContourSpace.lift γ (Z i) θ)))) := by
  obtain ⟨K, E, hElift, hLip, hc, hE⟩ :=
    S.exists_clamped_actualTorusCorrection_LittleField hS hwf hwper hwrot hmean
      hε hεT ha ha16 hsupp hγ1
  have hcomponent {Z : ι → LittleContourSpace γ} (hZ : Z ∈ ball 0 (a / 4)) (i : ι) :
      Z i ∈ ball 0 (a / 4) :=
    mem_ball_zero_iff.mpr ((norm_le_pi_norm Z i).trans_lt (mem_ball_zero_iff.mp hZ))
  refine ⟨K, (fun t Z i => E t (Z i)), ?_, ?_, ?_, ?_⟩
  · intro t
    apply LipschitzOnWith.of_dist_le_mul
    intro Z hZ W hW
    apply (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).mpr
    intro i
    exact ((hLip t).dist_le_mul (Z i) (hcomponent hZ i) (W i) (hcomponent hW i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist Z W i) K.2)
  · intro Z hZ
    exact continuous_pi_iff.mpr (fun i => hc (Z i) (hcomponent hZ i))
  · intro t Z hZ i θ
    exact hElift t (Z i) ((norm_le_pi_norm Z i).trans_lt hZ) θ
  · intro t ht Z hZ i θ
    rw [hE t ht (Z i) ((norm_le_pi_norm Z i).trans_lt hZ) θ,
      S.actualTorusCorrectionVelocity_physicalComplexSource hwf ⟨ht.1, ht.2.trans hεT⟩]

end BoundedEulerParticleSystem
end Euler2D

end
