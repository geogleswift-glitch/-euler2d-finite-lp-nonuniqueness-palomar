module

public import RequestProject.Euler.TorusClampedContourForcing
public import RequestProject.Euler.FiniteContourForcedLocalFlow

/-! A finite contour solution with the correction supplied by one genuine
torus Euler particle system. This constructs the forced contour solution;
identification of its transported density with that particle system is a
separate assertion. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) torusForcedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) torusForcedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) torusForcedC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) torusForcedC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_local_finiteContour_with_actual_correction
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (hmean : (∫ x in torusBox, f x) = 0)
    {ε a : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0)
    {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (hZ : IsAdmissibleLittleContourFamily Z₀ r Z)
    (hZa : ‖Z‖ < a / 4) :
    ∃ E : ℝ → LittleContourSpace γ → LittleContourSpace γ,
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ V, ‖V‖ < a / 4 → ∀ θ,
        LittleContourSpace.lift γ (E t V) θ =
          actualTorusCorrectionVelocity (S.physicalComplexSource w t)
            (LittleContourSpace.lift γ V θ)) ∧
      ∃ ρ > 0, ∃ δ > 0, δ ≤ ε ∧
      ∃ X : (ι → LittleContourSpace γ) → ℝ → ι → LittleContourSpace γ,
        IsNonautonomousBanachFlowOn
          (fun t W => finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g W +
            fun i => E t (W i))
          ({W | IsAdmissibleLittleContourFamily Z₀ r W} ∩ ball 0 (a / 4)) (ball Z ρ) δ X ∧
        ∀ W ∈ ball Z ρ, ∀ t ∈ Icc (0 : ℝ) δ, ∀ i θ,
          HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
            (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ +
              actualTorusCorrectionVelocity (S.physicalComplexSource w t)
                (LittleContourSpace.lift γ (X W t i) θ)) t := by
  obtain ⟨K, E, _, hLip, hc, hE⟩ :=
    S.exists_clamped_actualTorusCorrection_LittleField hS hwf hwper hwrot hmean
      hε hεT ha ha16 hsupp hγ1.le
  have hcomponent {W : ι → LittleContourSpace γ}
      (hW : W ∈ ball 0 (a / 4)) (i : ι) : W i ∈ ball 0 (a / 4) :=
    mem_ball_zero_iff.mpr ((norm_le_pi_norm W i).trans_lt (mem_ball_zero_iff.mp hW))
  have hELip (t : ℝ) (_ht : t ∈ Icc (-ε) ε) :
      LipschitzOnWith K (fun W : ι → LittleContourSpace γ => fun i => E t (W i))
        (ball 0 (a / 4)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro W hW V hV
    apply (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).mpr
    intro i
    exact ((hLip t).dist_le_mul (W i) (hcomponent hW i) (V i) (hcomponent hV i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist W V i) K.2)
  have hEc (W : ι → LittleContourSpace γ) (hW : W ∈ ball 0 (a / 4)) :
      ContinuousOn (fun t => fun i => E t (W i)) (Icc (-ε) ε) :=
    (continuous_pi_iff.mpr (fun i => hc (W i) (hcomponent hW i))).continuousOn
  have hU : ball (0 : ι → LittleContourSpace γ) (a / 4) ∈ 𝓝 Z :=
    isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hZa)
  obtain ⟨ρ, hρ, δ, hδ, hδε, X, hX, hderiv⟩ :=
    exists_finiteContour_forced_local_flow hγ hγ1 Z₀ r hr href g Z hZ
      (fun t W i => E t (W i)) hε hU hELip hEc
  refine ⟨E, hE, ρ, hρ, δ, hδ, hδε, X, hX, ?_⟩
  intro W hW t ht i θ
  have htε : t ∈ Icc (0 : ℝ) ε := ⟨ht.1, ht.2.trans hδε⟩
  have hi : ‖X W t i‖ < a / 4 :=
    mem_ball_zero_iff.mp (hcomponent (hX.mem W hW t ht).2 i)
  simpa only [hE t htε (X W t i) hi θ] using hderiv W hW t ht i θ

end BoundedEulerParticleSystem

end Euler2D

end
