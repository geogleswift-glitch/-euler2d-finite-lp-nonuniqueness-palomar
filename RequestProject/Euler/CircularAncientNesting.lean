module

public import RequestProject.Euler.CircularPhaseDomainTransport
public import RequestProject.Euler.CircularAncientMomentAsymptotic

/-! The actual ancient interfaces remain strictly nested. At sufficiently
negative full-period samples the genuine orbit is close to the two
reference circles. The same particle homeomorphism then transports both
domains to every subsequent negative time. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric Asymptotics
open scoped NNReal ENNReal

namespace Euler2D

theorem circular_domains_closure_nested_of_reference_near
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z : Fin 2 → LittleContourSpace γ)
    (hnear : ∀ i : Fin 2,
      ‖(Z i).val - (circularReferenceC1 hγ hγ1 i)‖ <
        min (cellA / 4) ((1 - cellA) / 4)) :
    closure (contourRadialFill (LittleContourSpace.lift γ (Z 0))) ⊆
      contourRadialFill (LittleContourSpace.lift γ (Z 1)) := by
  let e₀ : ℝ := ‖(Z 0).val - (circularReferenceC1 hγ hγ1 0)‖
  let e₁ : ℝ := ‖(Z 1).val - (circularReferenceC1 hγ hγ1 1)‖
  have he₀ : e₀ < min (cellA / 4) ((1 - cellA) / 4) := hnear 0
  have he₁ : e₁ < min (cellA / 4) ((1 - cellA) / 4) := hnear 1
  have hsmall₀ : e₀ ≤ circularContourRadii 0 / 4 := by
    simpa only [circularContourRadii, Matrix.cons_val_zero] using
      he₀.le.trans (min_le_left _ _)
  have hsmall₁ : e₁ ≤ circularContourRadii 1 / 4 := by
    have ha := cellA_lt_one
    have he := he₁.le.trans (min_le_left _ _)
    norm_num [circularContourRadii]
    linarith
  have hsub : contourRadialFill (LittleContourSpace.lift γ (Z 0)) ⊆
      Metric.closedBall 0 (cellA + e₀) := by
    change contourRadialFill (ContourC1Space.lift γ (Z 0).val) ⊆ _
    rw [← contourC1EnclosedDomain_eq_radialFill (Z 0).val
      (circularReferenceC1 hγ hγ1 0) (growingMoment_radius_pos 0)
      (lift_circularReferenceC1 hγ hγ1 0) hsmall₀]
    have hball := contourC1EnclosedDomain_subset_ball (Z 0).val (circularReferenceC1 hγ hγ1 0)
      (growingMoment_radius_pos 0) (lift_circularReferenceC1 hγ hγ1 0) hsmall₀
    simpa only [circularContourRadii, Matrix.cons_val_zero] using hball.trans ball_subset_closedBall
  have hclosed := closure_minimal hsub isClosed_closedBall
  have hgap : cellA + e₀ < 1 - e₁ := by
    have h₀ := he₀.trans_le (min_le_right _ _)
    have h₁ := he₁.trans_le (min_le_right _ _)
    have ha := cellA_lt_one
    linarith
  intro x hx
  change x ∈ contourRadialFill (ContourC1Space.lift γ (Z 1).val)
  rw [← contourC1EnclosedDomain_eq_radialFill (Z 1).val
    (circularReferenceC1 hγ hγ1 1) (growingMoment_radius_pos 1)
    (lift_circularReferenceC1 hγ hγ1 1) hsmall₁]
  apply ball_subset_contourC1EnclosedDomain (Z 1).val (circularReferenceC1 hγ hγ1 1)
    (growingMoment_radius_pos 1) (lift_circularReferenceC1 hγ hγ1 1) hsmall₁
  have hxnorm := mem_closedBall_zero_iff.mp (hclosed hx)
  simpa only [circularContourRadii, Matrix.cons_val_one, Matrix.cons_val_zero,
    mem_ball_zero_iff] using hxnorm.trans_lt hgap

theorem circularAncientMaterial_closure_nested
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Y : ℝ → Fin 2 → LittleContourSpace γ}
    (hYc : ContinuousOn Y (Iic (0 : ℝ)))
    (hYm : ∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1)
    (hYd : ∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s)
    (hLim : Tendsto (fun n : ℕ => Y (-(n : ℝ) * (period + period))) atTop
      (𝓝 (littleCircularReference hγ hγ1)))
    {t : ℝ} (ht : t ≤ 0) :
    closure (contourRadialFill (LittleContourSpace.lift γ (Y t 0))) ⊆
      contourRadialFill (LittleContourSpace.lift γ (Y t 1)) := by
  let e : ℝ := min (cellA / 4) ((1 - cellA) / 4)
  have he : 0 < e := lt_min (by have ha := cellA_pos; positivity) (by linarith [cellA_lt_one])
  have hnear : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 2,
      ‖(Y (-(n : ℝ) * (period + period)) i).val - circularReferenceC1 hγ hγ1 i‖ < e := by
    apply Filter.eventually_all.mpr
    intro i
    let pr : (Fin 2 → LittleContourSpace γ) →L[ℝ] ContourC1Space γ :=
      (LittleContourSpace.inclusion γ).comp (ContinuousLinearMap.proj i)
    have hl := (((pr.continuous.tendsto _).comp hLim).sub
      (tendsto_const_nhds (x := circularReferenceC1 hγ hγ1 i))).norm
    have hlimit : ‖pr (littleCircularReference hγ hγ1) - circularReferenceC1 hγ hγ1 i‖ < e := by
      change ‖(circularReferenceC1 hγ hγ1 i) - circularReferenceC1 hγ hγ1 i‖ < e
      simpa only [sub_self, norm_zero] using he
    have hev := hl.eventually (eventually_lt_nhds hlimit)
    simpa only [Function.comp_apply] using hev
  have hD : 0 < period + period := by unfold period; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (-t / (period + period))
  obtain ⟨n, hnnear, hnN⟩ := (hnear.and (eventually_ge_atTop N)).exists
  let a : ℝ := -(n : ℝ) * (period + period)
  have hat : a ≤ t := by
    have hNc : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have hNt : -t < (N : ℝ) * (period + period) := (div_lt_iff₀ hD).mp hN
    have hmul := mul_le_mul_of_nonneg_right hNc hD.le
    dsimp only [a]
    linarith
  have ha : a ≤ 0 := hat.trans ht
  let Z : ℝ → Fin 2 → LittleContourSpace γ := fun s => Y (s + a)
  have hsub {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (t - a)) : s + a ≤ 0 := by linarith [hs.2]
  have hZc : ContinuousOn Z (Icc (0 : ℝ) (t - a)) :=
    hYc.comp (continuous_id.add continuous_const).continuousOn (fun s hs => hsub hs)
  have hZm : ∀ s ∈ Icc (0 : ℝ) (t - a), Z s ∈ circularQuarterPhaseDomain hγ hγ1 :=
    fun s hs => hYm (s + a) (hsub hs)
  have hZd : ∀ s ∈ Icc (0 : ℝ) (t - a), HasDerivAt Z (circularBanachField hγ hγ1 (Z s)) s :=
    fun s hs => (hYd (s + a) (hsub hs)).comp_add_const s a
  obtain ⟨F, hFc, hFic, hF0, hFd, hFarea, hdomains⟩ :=
    exists_circularPhase_material_domain_transport hγ hγ1 Z (sub_nonneg.mpr hat) hZc hZm hZd
  have hdom (i : Fin 2) : F (t - a) '' contourRadialFill (LittleContourSpace.lift γ (Y a i)) =
      contourRadialFill (LittleContourSpace.lift γ (Y t i)) := by
    simpa only [Z, zero_add, sub_add_cancel] using
      hdomains (t - a) ⟨sub_nonneg.mpr hat, le_rfl⟩ i
  have hinitial := circular_domains_closure_nested_of_reference_near hγ hγ1 (Y a) hnnear
  rw [← hdom 0, ← (F (t - a)).image_closure, ← hdom 1]
  exact image_mono hinitial

theorem exists_circularAncientMaterial_fourthMoment_asymptotic_nested {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ Y : ℝ → Fin 2 → LittleContourSpace γ, ∃ κ : ℂ, ∃ δ > 0,
      κ ≠ 0 ∧ ContinuousOn Y (Iic 0) ∧
      (∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1) ∧
      (∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s) ∧
      Tendsto (fun n : ℕ => Y (-(n : ℝ) * (period + period))) atTop
        (𝓝 (littleCircularReference hγ hγ1)) ∧
      (∀ s ≤ 0, ∀ i, littleContourArea γ (Y s i) = Real.pi * circularContourRadii i ^ 2) ∧
      (∀ s ≤ 0, ∀ i, Y s i ∈ fourfoldLittleContourSubmodule γ) ∧
      (∀ s ≤ 0, closure (contourRadialFill (LittleContourSpace.lift γ (Y s 0))) ⊆
        contourRadialFill (LittleContourSpace.lift γ (Y s 1))) ∧
      (fun s : ℝ => circularBoundaryFourthMoment (Y s) - κ * Complex.exp ((s : ℂ) * lamStar)) =O[atBot]
        (fun s : ℝ => Real.exp ((sigma + δ) * s)) := by
  obtain ⟨Y, κ, δ, hδ, hκ, hYc, hYm, hYd, hLim, hArea, hFour, hAsym⟩ :=
    exists_circularAncientMaterial_fourthMoment_asymptotic_constrained hγ hγ1
  exact ⟨Y, κ, δ, hδ, hκ, hYc, hYm, hYd, hLim, hArea, hFour,
    fun s hs => circularAncientMaterial_closure_nested hγ hγ1 hYc hYm hYd hLim hs, hAsym⟩

end Euler2D

end
