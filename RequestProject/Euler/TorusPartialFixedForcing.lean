module

public import RequestProject.Euler.TorusInnerLabelFixedForcing
public import RequestProject.Euler.TorusFinitePhaseFixedForcing

/-! A single actual partial forcing: the transported inner source plus
the Green correction of the same Euler system. Both local state bounds
and finite tube bounds are derived from the two genuine fields. -/

@[expose] public section

set_option maxHeartbeats 4500000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_finitePhase_fixed_partial_forcing
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (hmean : (∫ x in torusBox, f x) = 0)
    {q : R2 → ℝ} {M : ℝ} (hq : MemLp q 2 μT) (hqper : IsTorusPeriodic q)
    (hqrot : ∀ x, q (torusQuarterTurn x) = q x)
    (hqmean : (∫ x in torusBox, q x) = 0) (hM : ∀ x, ‖q x‖ ≤ M)
    {ε a ai L : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0)
    (hai : 0 ≤ ai) (hai1 : ai < 1)
    (hinner : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      ai < ‖x - torusCenter‖ → S.transportedScalar q t x = 0)
    (hL : 0 ≤ L) (hLa : L < a / 4)
    {γ : ℝ≥0} {ι : Type} [Fintype ι] (hγ1 : (γ : ℝ) ≤ 1)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (hsep : ∀ i, 16 * ai ≤ d i) :
    ∃ E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ,
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ W, ‖W‖ < a / 4 →
        (∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) → ∀ i θ,
        LittleContourSpace.lift γ (E t W i) θ =
          S.physicalLabelComplexField q t (LittleContourSpace.lift γ (W i) θ)) ∧
      (∀ W, ‖W‖ < a / 4 →
        (∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) →
          Continuous (fun t => E t W)) ∧
      (∀ Z, ‖Z‖ < a / 4 → (∀ i x, d i ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖) →
        ∃ K : ℝ≥0, ∃ V : Set (ι → LittleContourSpace γ), V ∈ 𝓝 Z ∧
          (∀ t, LipschitzOnWith K (E t) V) ∧
            ∀ W ∈ V, Continuous (fun t => E t W)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) ε, ∀ W, ‖W‖ ≤ L →
        (∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) → ‖E t W‖ ≤ B := by
  obtain ⟨Kc, Ec, hEcLip, hEcc, _hEcraw, hEc⟩ := S.exists_finitePhase_fixed_actual_forcing
    (ι := ι) hS hwf hwper hwrot hmean hε hεT ha ha16 hsupp hγ1
  obtain ⟨Ei, hEi, hEic, hEiloc, hEinorm⟩ := S.exists_finitePhase_fixed_actualInner_forcing
    hS hq hqper hqrot hqmean hM hε hεT hai hai1 hinner hγ1 d hd hsep
  let E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ := fun t W => Ei t W + Ec t W
  have htime (W : ι → LittleContourSpace γ) (hWa : ‖W‖ < a / 4)
      (hW : ∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) :
      Continuous (fun t => E t W) :=
    (hEic W hW).add (hEcc W (mem_ball_zero_iff.mpr hWa))
  refine ⟨E, ?_, htime, ?_, ?_⟩
  · intro t ht W hWa hW i θ
    change LittleContourSpace.lift γ (Ei t W i) θ + LittleContourSpace.lift γ (Ec t W i) θ = _
    rw [hEi t W hW i θ, projIcc_of_mem hε.le ht, hEc t ht W hWa i θ,
      S.physicalLabelComplexField_eq]
  · intro Z hZa hZ
    obtain ⟨Ki, Ui, hUi, hEiLip⟩ := hEiloc Z hZ
    let Vd : Set (ι → LittleContourSpace γ) := {W | ∀ i, W i ∈ ball (Z i) (d i / 4)}
    have hVdopen : IsOpen Vd := by
      have hi (i : ι) : IsOpen {W : ι → LittleContourSpace γ | W i ∈ ball (Z i) (d i / 4)} :=
        isOpen_ball.preimage (continuous_apply i)
      simpa only [Vd, setOf_forall] using isOpen_iInter_of_finite hi
    have hVd : Vd ∈ 𝓝 Z := hVdopen.mem_nhds
      (fun i => mem_ball_self (div_pos (hd i) (by norm_num)))
    have htarget {W : ι → LittleContourSpace γ} (hW : W ∈ Vd) (i : ι) (x : ContourCircle) :
        d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖ := by
      have he : ‖(W i).val - (Z i).val‖ < d i / 4 := by
        simpa only [dist_eq_norm] using mem_ball.mp (hW i)
      have hev := (ContourC1Space.norm_eval_le ((W i).val - (Z i).val) x).trans_lt he
      change ‖ContourC1Space.toBCF γ (W i).val x - ContourC1Space.toBCF γ (Z i).val x‖ < d i / 4 at hev
      have hn := norm_sub_norm_le (ContourC1Space.toBCF γ (Z i).val x)
        (ContourC1Space.toBCF γ (W i).val x)
      rw [norm_sub_rev] at hn
      have hz := hZ i x
      have hdi := hd i
      linarith
    let V : Set (ι → LittleContourSpace γ) := Ui ∩ (ball 0 (a / 4) ∩ Vd)
    have hV : V ∈ 𝓝 Z := inter_mem hUi
      (inter_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hZa)) hVd)
    refine ⟨Ki + Kc, V, hV, ?_, ?_⟩
    · intro t
      exact ((hEiLip t).mono inter_subset_left).add ((hEcLip t).mono (fun _ h => h.2.1))
    · intro W hW
      exact htime W (mem_ball_zero_iff.mp hW.2.1) (htarget hW.2.2)
  · have hzero : (0 : ι → LittleContourSpace γ) ∈ ball 0 (a / 4) := mem_ball_self (by positivity)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hEcc 0 hzero).continuousOn
    let M₄ := ai ^ 4 * ∫ x in torusBox, |q x|
    have hM₄ : 0 ≤ M₄ := by dsimp only [M₄]; positivity
    let B : ι → ℝ := fun i => cauchyContourNormBudget 5 (γ : ℝ) M₄ (d i / 2) L
    have hB (i : ι) : 0 ≤ B i := by
      have hdi := hd i
      dsimp only [B, cauchyContourNormBudget, cauchySpatialDerivativeBudget]
      positivity
    let BI := ∑ i, B i
    have hBI : 0 ≤ BI := Finset.sum_nonneg (fun i _ => hB i)
    refine ⟨BI + ((Kc : ℝ) * L + |C|), by positivity, ?_⟩
    intro t ht W hWL hW
    have hWin : W ∈ ball 0 (a / 4) := mem_ball_zero_iff.mpr (hWL.trans_lt hLa)
    have hEiB : ‖Ei t W‖ ≤ BI := by
      apply (pi_norm_le_iff_of_nonneg hBI).mpr
      intro i
      have hn := (hEinorm t W hW i).trans
        (cauchyContourNormBudget_mono_length 5 (γ : ℝ) hM₄ (half_pos (hd i))
          (norm_nonneg _) ((norm_le_pi_norm W i).trans hWL))
      exact hn.trans (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i))
    have hh := (hEcLip t).dist_le_mul W hWin 0 hzero
    simp only [dist_eq_norm, sub_zero] at hh
    have hEcB : ‖Ec t W‖ ≤ (Kc : ℝ) * L + |C| :=
      (norm_le_norm_sub_add (Ec t W) (Ec t 0)).trans
        (add_le_add (hh.trans (mul_le_mul_of_nonneg_left hWL Kc.2))
          ((hC t ht).trans (le_abs_self C)))
    exact (norm_add_le _ _).trans (add_le_add hEiB hEcB)

end BoundedEulerParticleSystem
end Euler2D

end
