module

public import RequestProject.Euler.CircularPeriodUnstableDirection

/-! Actual fixed-area, fourfold initial curves in the unstable direction,
and genuine nonlinear one-period growth for all sufficiently small
nonzero values of their real parameter. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) growingInitialLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) growingInitialLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularGrowingInitial {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (s : ℝ) (i : Fin 2) : LittleContourSpace γ :=
  littleAreaChart hγ hγ1.le (circularContourRadii i)
    (s • circularGrowingVariation hγ hγ1 0 i)

theorem circularGrowingInitial_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    circularGrowingInitial hγ hγ1 0 = littleCircularReference hγ hγ1 := by
  funext i
  simp only [circularGrowingInitial, zero_smul, littleAreaChart_zero]
  rfl

theorem circularGrowingInitial_hasDerivAt_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    HasDerivAt (circularGrowingInitial hγ hγ1) (circularGrowingVariation hγ hγ1 0) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have hl : HasDerivAt (fun s : ℝ => s • circularGrowingVariation hγ hγ1 0 i)
      (circularGrowingVariation hγ hγ1 0 i) 0 := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      (ContinuousLinearMap.toSpanSingleton ℝ
        (circularGrowingVariation hγ hγ1 0 i)).hasDerivAt (x := (0 : ℝ))
  have hc : HasFDerivAt (littleAreaChart hγ hγ1.le (circularContourRadii i))
      (ContinuousLinearMap.id ℝ (LittleContourSpace γ))
      ((0 : ℝ) • circularGrowingVariation hγ hγ1 0 i) := by
    simpa only [zero_smul] using hasFDerivAt_littleAreaChart_zero hγ hγ1.le (circularContourRadii i)
  simpa only [Function.comp_def, ContinuousLinearMap.id_apply] using hc.comp_hasDerivAt 0 hl

theorem circularGrowingInitial_fourfold {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (s : ℝ) (i : Fin 2) :
    circularGrowingInitial hγ hγ1 s i ∈ fourfoldLittleContourSubmodule γ :=
  littleAreaChart_mem_fourfold hγ hγ1.le _ _
    ((fourfoldLittleContourSubmodule γ).smul_mem s
      (circularGrowingVariation_mem_fourfold_area hγ hγ1 i).1)

theorem eventually_circularGrowingInitial_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∀ᶠ s : ℝ in 𝓝 0, ∀ i : Fin 2,
      loopArea (LittleContourSpace.lift γ (circularGrowingInitial hγ hγ1 s i)) =
        Real.pi * circularContourRadii i ^ 2 := by
  apply Filter.eventually_all.mpr
  intro i
  have hr : circularContourRadii i ≠ 0 := by
    fin_cases i <;> norm_num [circularContourRadii, cellA_pos.ne']
  obtain ⟨ε, hε, hchart⟩ := exists_littleFixedAreaChart_radius hγ hγ1.le hr
  have hc : Continuous (fun s : ℝ => s • circularGrowingVariation hγ hγ1 0 i) :=
    continuous_id.smul continuous_const
  have hs : ∀ᶠ s : ℝ in 𝓝 0,
      s • circularGrowingVariation hγ hγ1 0 i ∈ ball (0 : LittleContourSpace γ) ε :=
    hc.continuousAt (by simpa only [zero_smul] using ball_mem_nhds (0 : LittleContourSpace γ) hε)
  filter_upwards [hs] with s hs
  exact (hchart _ (by simpa only [mem_ball, dist_zero_right] using hs) (by
    rw [map_smul]
    have hz : littleContourEllCLM γ (circularContourRadii i)
        (circularGrowingVariation hγ hγ1 0 i) = 0 :=
      (circularGrowingVariation_mem_fourfold_area hγ hγ1 i).2
    rw [hz, smul_zero])).2

theorem eventually_circularGrowingInitial_mem_ball {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ s : ℝ in 𝓝 0, circularGrowingInitial hγ hγ1 s ∈
      ball (littleCircularReference hγ hγ1) ρ :=
  (circularGrowingInitial_hasDerivAt_zero hγ hγ1).continuousAt
    (by rw [circularGrowingInitial_zero]; exact ball_mem_nhds _ hρ)

theorem eventually_norm_sub_lt_of_derivative_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : ℝ → E} {u v a : E} (hF : HasDerivAt F u 0) (hG : HasDerivAt G v 0)
    (hF0 : F 0 = a) (hG0 : G 0 = a) (hvu : ‖v‖ < ‖u‖) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖G t - a‖ < ‖F t - a‖ := by
  have he : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖slope G 0 t‖ - ‖slope F 0 t‖ < 0 :=
    (hG.tendsto_slope.norm.sub hF.tendsto_slope.norm).eventually
      (eventually_lt_nhds (sub_neg.mpr hvu))
  filter_upwards [he, self_mem_nhdsWithin] with t ht ht0
  have htne : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using ht0
  have hp : 0 < |t|⁻¹ := inv_pos.mpr (abs_pos.mpr htne)
  simp only [slope_def_module, sub_zero, hF0, hG0, norm_smul,
    norm_inv, Real.norm_eq_abs] at ht
  nlinarith [sub_neg.mp ht]

set_option maxHeartbeats 800000 in
theorem circularGrowingInitial_return_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hP : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :
    HasDerivAt (fun s => X (circularGrowingInitial hγ hγ1 s) period)
      ((-lamMult : ℝ) • circularGrowingVariation hγ hγ1 0) 0 := by
  have hp : HasFDerivAt (fun W => X W period)
      (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
      (circularGrowingInitial hγ hγ1 0) := by
    rw [circularGrowingInitial_zero]
    exact hP.hasFDerivAt
  have hd := hp.comp_hasDerivAt 0 (circularGrowingInitial_hasDerivAt_zero hγ hγ1)
  simpa only [Function.comp_def, circularPeriod_derivative_growing hγ hγ1 hρ hX] using hd

set_option maxHeartbeats 800000 in
theorem eventually_circularGrowingInitial_return_growth {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hP : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1) :
    ∀ᶠ s : ℝ in 𝓝[≠] 0,
      ‖circularGrowingInitial hγ hγ1 s - littleCircularReference hγ hγ1‖ <
        ‖X (circularGrowingInitial hγ hγ1 s) period - littleCircularReference hγ hγ1‖ := by
  apply eventually_norm_sub_lt_of_derivative_growth
    (circularGrowingInitial_return_hasDerivAt hγ hγ1 hρ hX hP)
    (circularGrowingInitial_hasDerivAt_zero hγ hγ1)
  · rwa [circularGrowingInitial_zero]
  · exact circularGrowingInitial_zero hγ hγ1
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (lt_trans zero_lt_one one_lt_lamMult)]
    simpa only [one_mul] using mul_lt_mul_of_pos_right one_lt_lamMult
      (norm_pos_iff.mpr (circularGrowingVariation_ne_zero hγ hγ1))

end Euler2D

end
