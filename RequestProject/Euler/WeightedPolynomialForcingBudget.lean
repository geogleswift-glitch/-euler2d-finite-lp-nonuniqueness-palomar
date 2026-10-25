module

public import RequestProject.Euler.PolynomialForcingTail

/-! A fixed polynomial forcing bound has a uniformly small weighted
tail on every actual finite path, with the entrance selected before
rho and before the finite endpoint. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology MeasureTheory

namespace Euler2D

theorem weighted_polynomial_forcing_finite_tail
    {E : Type*} [NormedAddCommGroup E] {σ S H B ρ : ℝ}
    (hσ : 0 < σ) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (q : ℝ → E) (hq : ContinuousOn q (Icc S H))
    (hbound : ∀ u ∈ Icc S H, ‖q u‖ ≤ B * ρ ^ 6 * (1 + u) ^ 4) :
    (∫ u in Icc S H, Real.exp (-σ * u) * ‖q u‖) ≤
      B * ρ ^ 6 * polynomialForcingTail σ S := by
  have he : Continuous (fun u : ℝ => Real.exp (-σ * u)) := by fun_prop
  have hf : IntegrableOn (fun u => Real.exp (-σ * u) * ‖q u‖) (Icc S H) :=
    (he.continuousOn.mul hq.norm).integrableOn_compact isCompact_Icc
  have hgc : Continuous (fun u : ℝ => (B * ρ ^ 6) * (Real.exp (-σ * u) * (1 + u) ^ 4)) := by fun_prop
  have hg : IntegrableOn (fun u : ℝ => (B * ρ ^ 6) * (Real.exp (-σ * u) * (1 + u) ^ 4)) (Icc S H) :=
    hgc.continuousOn.integrableOn_compact isCompact_Icc
  have htail : (∫ u in Icc S H, Real.exp (-σ * u) * (1 + u) ^ 4) ≤ polynomialForcingTail σ S := by
    apply setIntegral_mono_set
      ((integrableOn_exponential_polynomial_four hσ).mono_set (Ici_subset_Ici.mpr hS))
      (ae_of_all _ (fun u => by positivity))
    exact ae_of_all _ (fun u hu => hu.1)
  calc
    _ ≤ ∫ u in Icc S H, (B * ρ ^ 6) * (Real.exp (-σ * u) * (1 + u) ^ 4) := by
      apply integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      calc
        _ ≤ Real.exp (-σ * u) * (B * ρ ^ 6 * (1 + u) ^ 4) :=
          mul_le_mul_of_nonneg_left (hbound u hu) (Real.exp_pos (-σ * u)).le
        _ = _ := by ring
    _ = (B * ρ ^ 6) * ∫ u in Icc S H, Real.exp (-σ * u) * (1 + u) ^ 4 := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)

theorem exists_fixed_polynomial_forcing_tail_entrance
    {E : Type*} [NormedAddCommGroup E] {σ B κ θ : ℝ}
    (hσ : 0 < σ) (hB : 0 ≤ B) (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (ρ H : ℝ) (q : ℝ → E),
      ContinuousOn q (Icc S H) →
      (∀ u ∈ Icc S H, ‖q u‖ ≤ B * ρ ^ 6 * (1 + u) ^ 4) →
      (∫ u in Icc S H, Real.exp (-σ * u) * ‖q u‖) ≤ θ * κ * ρ ^ 6 := by
  have hh := (tendsto_polynomialForcingTail hσ).const_mul B
  simp only [mul_zero] at hh
  obtain ⟨S, hS, htail⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hh.eventually (gt_mem_nhds (mul_pos hθ hκ)))).exists
  refine ⟨S, hS, ?_⟩
  intro ρ H q hq hbound
  calc
    _ ≤ B * ρ ^ 6 * polynomialForcingTail σ S :=
      weighted_polynomial_forcing_finite_tail hσ hS hB q hq hbound
    _ = (B * polynomialForcingTail σ S) * ρ ^ 6 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htail.le (by positivity)

end Euler2D

end
