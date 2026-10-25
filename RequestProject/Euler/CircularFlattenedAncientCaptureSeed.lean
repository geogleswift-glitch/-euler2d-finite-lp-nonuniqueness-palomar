module

public import RequestProject.Euler.CircularRobustFlattenedAncientSamples
public import RequestProject.Euler.CircularMaterialTransferProfile
public import RequestProject.Euler.CircularActualConstraintChart

/-! The original ancient samples give genuine nonzero unstable seeds
on the same backward graph. Their flattened complement is exactly zero,
and their unstable coordinate tends to zero. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric Asymptotics
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) ancientSeedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) ancientSeedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) ancientSeedFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) ancientSeedTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) ancientSeedTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) ancientSeedTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem LaplaceHyp.eventually_norm_lower_bound {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (h : LaplaceHyp σ ν δ d κ N) :
    ∀ᶠ s : ℝ in atBot, ‖κ‖ / 2 * Real.exp (σ * s) ≤ ‖N s‖ := by
  obtain ⟨C, hC, hbound⟩ := h.bot.exists_pos
  have hκ : 0 < ‖κ‖ := norm_pos_iff.mpr h.kappa_ne
  have hlim : Tendsto (fun s : ℝ => C * Real.exp (δ * s)) atBot (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos h.delta_pos).mpr tendsto_id)).const_mul C
  filter_upwards [hbound.bound, hlim.eventually (eventually_lt_nhds (half_pos hκ))] with s hs hsmall
  have heq : Real.exp ((σ + δ) * s) = Real.exp (δ * s) * Real.exp (σ * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have herr : ‖N s - κ * Complex.exp ((σ + ν * I) * s)‖ ≤ ‖κ‖ / 2 * Real.exp (σ * s) := by
    have hrem := hs
    rw [Real.norm_eq_abs, Real.abs_exp, heq, ← mul_assoc] at hrem
    exact hrem.trans (mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos _).le)
  have hlead : ‖κ * Complex.exp ((σ + ν * I) * s)‖ = ‖κ‖ * Real.exp (σ * s) := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have htriangle : ‖κ‖ * Real.exp (σ * s) ≤ ‖N s‖ + ‖N s - κ * Complex.exp ((σ + ν * I) * s)‖ := by
    rw [← hlead]
    calc
      _ = ‖N s - (N s - κ * Complex.exp ((σ + ν * I) * s))‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith only [herr, htriangle]

theorem circularConstraintProjection_chart_identity {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (v : CircularConstrainedTangentSpace γ) :
    circularConstraintProjectionToTangentCLM hγ hγ1.le
      (circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1) = v := by
  apply Subtype.ext
  rw [circularConstraintProjectionToTangentCLM_val,
    circularConstraintProjection_sub_reference hγ hγ1 _ (circularConstrainedChart_fourfold hγ hγ1 v),
    circularAreaChartInverseFamily_chart]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem ancient_moment_eventually_ne_zero :
    ∀ᶠ s : ℝ in atBot, s ≤ 0 ∧ P.ancient s ≠ littleCircularReference hγ hγ1 := by
  filter_upwards [P.laplace.eventually_norm_lower_bound, eventually_le_atBot (0 : ℝ)] with s hs hs0
  refine ⟨hs0, ?_⟩
  intro he
  have hn : 0 < ‖P.moment s‖ :=
    (mul_pos (half_pos (norm_pos_iff.mpr P.laplace.kappa_ne)) (Real.exp_pos _)).trans_le hs
  rw [P.moment_negative s hs0, he, circularBoundaryFourthMoment_reference, norm_zero] at hn
  exact (lt_irrefl 0) hn

theorem ancient_unstable_samples_tendsto_zero :
    Tendsto (fun n : ℕ => circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (P.ancient (-(n : ℝ) * (period + period)) - littleCircularReference hγ hγ1)))
      atTop (𝓝 0) := by
  have hv := (circularConstraintProjectionToTangentCLM hγ hγ1.le).continuous.tendsto 0
  have hp := (circularConstrainedUnstableProjectionCLM hγ hγ1.le).continuous.tendsto 0
  have hlim : Tendsto (fun n : ℕ => P.ancient (-(n : ℝ) * (period + period)) - littleCircularReference hγ hγ1)
      atTop (𝓝 0) := by
    simpa only [sub_self] using P.ancient_samples_tendsto.sub_const (littleCircularReference hγ hγ1)
  have hvlim : Tendsto (fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
      (P.ancient (-(n : ℝ) * (period + period)) - littleCircularReference hγ hγ1)) atTop (𝓝 0) := by
    simpa only [map_zero] using hv.comp hlim
  simpa only [map_zero] using hp.comp hvlim

theorem ancient_flattened_samples_eventually_seed
    {F : CircularConstrainedTangentSpace γ → CircularConstrainedTangentSpace γ} {r : ℝ}
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph F (circularConstrainedUnstableProjectionCLM hγ hγ1.le)
      circularAncientBackwardWeight r x)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (x α 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      let s := -(n : ℝ) * (period + period)
      let v := circularConstraintProjectionToTangentCLM hγ hγ1.le (P.ancient s - littleCircularReference hγ hγ1)
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      s ≤ 0 ∧ 0 < ‖α‖ ∧ ‖α‖ < ε ∧ ‖α‖ ≤ r / 2 ∧
        v = x α 0 ∧ (v - α) - (x α 0 - α) = 0 := by
  obtain ⟨N, hN⟩ := hsamples
  have hperiod : 0 < period := by unfold period; positivity
  have ht : Tendsto (fun n : ℕ => -(n : ℝ) * (period + period)) atTop atBot := by
    have hh : Tendsto (fun n : ℕ => (n : ℝ) * (period + period)) atTop atTop :=
      (tendsto_mul_const_atTop_of_pos (add_pos hperiod hperiod)).mpr tendsto_natCast_atTop_atTop
    simpa only [neg_mul] using tendsto_neg_atTop_atBot.comp hh
  have hlim : Tendsto (fun n : ℕ => ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (P.ancient (-(n : ℝ) * (period + period)) - littleCircularReference hγ hγ1))‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using P.ancient_unstable_samples_tendsto_zero.norm
  have hsmall := hlim.eventually (eventually_lt_nhds hε)
  filter_upwards [eventually_ge_atTop N, ht.eventually P.ancient_moment_eventually_ne_zero, hsmall] with n hn hne hnsmall
  dsimp only
  obtain ⟨α, hα, hαr, hs⟩ := hN n hn
  have hv : circularConstraintProjectionToTangentCLM hγ hγ1.le
      (P.ancient (-(n : ℝ) * (period + period)) - littleCircularReference hγ hγ1) = x α 0 := by
    rw [hs, circularConstraintProjection_chart_identity]
  have hcoord := hg.coordinate α hα hαr
  have hαne : α ≠ 0 := by
    intro hz
    have hnorm := hg.norm_le α hα hαr 0
    have hx : x α 0 = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [hz, norm_zero, mul_zero] using hnorm) (norm_nonneg _)
    apply hne.2
    rw [hs, hx, circularConstrainedChart_zero]
  have hseed := norm_pos_iff.mpr hαne
  rw [hv, hcoord] at hnsmall ⊢
  exact ⟨hne.1, hseed, hnsmall, hαr, rfl, sub_self _⟩

end CircularMaterialTransferProfile
end Euler2D

end
