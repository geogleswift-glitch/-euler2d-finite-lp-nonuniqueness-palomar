module

public import RequestProject.Euler.TorusClampedContourForcing
public import RequestProject.Euler.FinitePhaseForcedLocalFlow
public import RequestProject.Euler.TorusPhysicalCorrectionIdentity

/-! The same actual torus correction gives genuine finite material
solutions at every phase, retaining a strict quarter-radius chart
neighborhood and the original literal label-integral correction. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) torusForcedPhaseLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) torusForcedPhaseLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) torusForcedPhaseC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) torusForcedPhaseC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

def IsQuarterPhaseLittleContourFamily {γ : ℝ≥0} {ι : Type*}
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (Z : ι → LittleContourSpace γ) : Prop :=
  ∃ b : ι → ℝ, ∀ i, ‖contourParameterShiftC1 (b i) (Z i).val - Z₀ i‖ < r i / 4

theorem isOpen_quarterPhaseLittleContourFamilies {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) :
    IsOpen {Z : ι → LittleContourSpace γ | IsQuarterPhaseLittleContourFamily Z₀ r Z} := by
  have he : {Z : ι → LittleContourSpace γ | IsQuarterPhaseLittleContourFamily Z₀ r Z} =
      ⋃ b : ι → ℝ, {Z : ι → LittleContourSpace γ |
        ∀ i, ‖contourParameterShiftC1 (b i) (Z i).val - Z₀ i‖ < r i / 4} := by
    ext Z
    simp only [IsQuarterPhaseLittleContourFamily, mem_setOf_eq, mem_iUnion]
  rw [he]
  apply isOpen_iUnion
  intro b
  have hi (i : ι) : IsOpen {Z : ι → LittleContourSpace γ |
      ‖contourParameterShiftC1 (b i) (Z i).val - Z₀ i‖ < r i / 4} :=
    isOpen_lt (((contourParameterShiftC1CLM γ (b i)).continuous.comp
      ((LittleContourSpace.inclusion γ).continuous.comp (continuous_apply i))).sub continuous_const).norm
      continuous_const
  simpa only [setOf_forall] using isOpen_iInter_of_finite hi

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_local_finitePhase_with_actual_correction
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
    (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z)
    (hZq : IsQuarterPhaseLittleContourFamily Z₀ r Z) (hZa : ‖Z‖ < a / 4) :
    ∃ δ > 0, δ ≤ ε ∧
      ∃ X : (ι → LittleContourSpace γ) → ℝ → ι → LittleContourSpace γ,
        ∃ ρ > 0,
          (∀ W ∈ ball Z ρ, X W 0 = W) ∧
          (∀ W ∈ ball Z ρ, ContinuousOn (X W) (Icc (0 : ℝ) δ)) ∧
          (∀ W ∈ ball Z ρ, ∀ t ∈ Icc (0 : ℝ) δ,
            IsPhaseAdmissibleLittleContourFamily Z₀ r (X W t) ∧
            ‖X W t‖ < a / 4 ∧ IsQuarterPhaseLittleContourFamily Z₀ r (X W t)) ∧
          ∀ W ∈ ball Z ρ, ∀ t ∈ Icc (0 : ℝ) δ, ∀ i θ,
            HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
              (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ +
                planeComplexEquiv (S.correctionLabelField t
                  (complexTorusPoint (LittleContourSpace.lift γ (X W t i) θ)))) t := by
  obtain ⟨K, E, _, hLip, hc, hE⟩ :=
    S.exists_clamped_actualTorusCorrection_LittleField hS hwf hwper hwrot hmean
      hε hεT ha ha16 hsupp hγ1.le
  let U : Set (ι → LittleContourSpace γ) := ball 0 (a / 4) ∩
    {W | IsQuarterPhaseLittleContourFamily Z₀ r W}
  have hcomponent {W : ι → LittleContourSpace γ} (hW : W ∈ ball 0 (a / 4)) (i : ι) :
      W i ∈ ball 0 (a / 4) :=
    mem_ball_zero_iff.mpr ((norm_le_pi_norm W i).trans_lt (mem_ball_zero_iff.mp hW))
  have hELip (t : ℝ) (_ht : t ∈ Icc (-ε) ε) :
      LipschitzOnWith K (fun W : ι → LittleContourSpace γ => fun i => E t (W i)) U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro W hW V hV
    apply (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).mpr
    intro i
    exact ((hLip t).dist_le_mul (W i) (hcomponent hW.1 i) (V i) (hcomponent hV.1 i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist W V i) K.2)
  have hEc (W : ι → LittleContourSpace γ) (hW : W ∈ U) :
      ContinuousOn (fun t => fun i => E t (W i)) (Icc (-ε) ε) :=
    (continuous_pi_iff.mpr (fun i => hc (W i) (hcomponent hW.1 i))).continuousOn
  have hU : U ∈ 𝓝 Z := inter_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hZa))
    ((isOpen_quarterPhaseLittleContourFamilies Z₀ r).mem_nhds hZq)
  obtain ⟨ρ, hρ, δ, hδ, hδε, X, hX, hderiv⟩ :=
    exists_finitePhase_forced_local_flow hγ hγ1 Z₀ r hr href g Z hZ
      (fun t W i => E t (W i)) hε hU hELip hEc
  refine ⟨δ, hδ, hδε, X, ρ, hρ, hX.initial, hX.continuous, ?_, ?_⟩
  · intro W hW t ht
    exact ⟨(hX.mem W hW t ht).1,
      mem_ball_zero_iff.mp (hX.mem W hW t ht).2.1, (hX.mem W hW t ht).2.2⟩
  · intro W hW t ht i θ
    have htε : t ∈ Icc (0 : ℝ) ε := ⟨ht.1, ht.2.trans hδε⟩
    have hi : ‖X W t i‖ < a / 4 :=
      mem_ball_zero_iff.mp (hcomponent (hX.mem W hW t ht).2.1 i)
    have hd := hderiv W hW t ht i θ
    rw [hE t htε (X W t i) hi θ,
      S.actualTorusCorrectionVelocity_physicalComplexSource hwf ⟨ht.1, htε.2.trans hεT⟩] at hd
    exact hd

end BoundedEulerParticleSystem
end Euler2D

end
