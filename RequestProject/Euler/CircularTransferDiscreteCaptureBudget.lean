module

public import RequestProject.Euler.CircularTransferFixedEntry
public import RequestProject.Euler.CapturePolynomialBlockBudget

/-! The same genuine late transfer entrance gives both its nonzero
rho-six seed and the source budget required by the finite capture
recurrence. The finite endpoint is chosen afterwards. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators NNReal

namespace Euler2D

theorem polynomial_point_le_scaled_forcing_tail {σ S : ℝ} (hσ : 0 < σ) (hS : 0 ≤ S) :
    (1 + S) ^ 4 ≤ Real.exp σ *
      (Real.exp (σ * S) * polynomialForcingTail σ S) := by
  let f : ℝ → ℝ := fun u => Real.exp (-σ * u) * (1 + u) ^ 4
  let c := Real.exp (-σ * (S + 1)) * (1 + S) ^ 4
  have hfc : Continuous f := by fun_prop
  have hfI : IntegrableOn f (Icc S (S + 1)) := hfc.continuousOn.integrableOn_compact isCompact_Icc
  have hcI : IntegrableOn (fun _ : ℝ => c) (Icc S (S + 1)) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint (u : ℝ) (hu : u ∈ Icc S (S + 1)) : c ≤ f u := by
    have he : Real.exp (-σ * (S + 1)) ≤ Real.exp (-σ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu.2 (by linarith))
    have hp : (1 + S) ^ 4 ≤ (1 + u) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith only [hu.1]) 4
    exact mul_le_mul he hp (by positivity) (Real.exp_pos _).le
  have hunit : c ≤ ∫ u in Icc S (S + 1), f u := by
    have hh : (∫ _u in Icc S (S + 1), c) ≤ ∫ u in Icc S (S + 1), f u := by
      apply integral_mono_ae hcI hfI
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact hpoint u hu
    simpa only [integral_const, Measure.real_def, Measure.restrict_apply_univ, Real.volume_Icc,
      show S + 1 - S = 1 by ring, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using hh
  have htail : (∫ u in Icc S (S + 1), f u) ≤ polynomialForcingTail σ S := by
    apply setIntegral_mono_set
      ((integrableOn_exponential_polynomial_four hσ).mono_set (Ici_subset_Ici.mpr hS))
      (ae_of_all _ (fun u => by dsimp only [f]; positivity))
    exact ae_of_all _ (fun u hu => hu.1)
  have hh := mul_le_mul_of_nonneg_left (hunit.trans htail) (Real.exp_pos (σ * (S + 1))).le
  have he : Real.exp (σ * (S + 1)) * Real.exp (-σ * (S + 1)) = 1 := by
    rw [← Real.exp_add, show σ * (S + 1) + -σ * (S + 1) = 0 by ring, Real.exp_zero]
  have he' : Real.exp (σ * (S + 1)) = Real.exp σ * Real.exp (σ * S) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [c] at hh
  rw [← mul_assoc, he, one_mul, he'] at hh
  simpa only [mul_assoc] using hh

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_fixed_transfer_entry_and_discrete_capture_budget {b B θ lam Tsrc : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) (1 / 4))
    (hne : bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0)
    (hB : 0 ≤ B) (hθ : 0 < θ) (hlam : 1 < lam) (hT : 0 ≤ Tsrc) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∃ H : ℝ, 0 < H ∧
      H = (‖Kstar * bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I))‖ / 4) *
        Real.exp (b * sigma * s₀) ∧
      (∀ ρ : ℝ, 0 ≤ ρ → 2 * H * ρ ^ 6 ≤
        ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀‖) ∧
      (∀ (ρ : ℝ) (W : ℂ), 0 ≤ ρ →
        ‖W - retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀‖ ≤ H * ρ ^ 6 → H * ρ ^ 6 ≤ ‖W‖) ∧
      ∀ (ρ : ℝ) (N : ℕ),
        (∑ j ∈ Finset.range N, (B * ρ ^ 6 * (1 + s₀ + ((j + 1 : ℕ) : ℝ) * Tsrc) ^ 4) /
          lam ^ (j + 1)) ≤ θ * H * ρ ^ 6 := by
  obtain ⟨F, hF, hfinite⟩ := exists_capture_polynomial_block_budget hlam hT
  obtain ⟨s₀, hs₀, H, hH, heq, hseed, hstable, htail⟩ :=
    P.exists_fixed_transfer_entry_and_polynomial_tail (B := F * B * Real.exp (b * sigma)) hb hne
      (by positivity) hθ
  refine ⟨s₀, hs₀, H, hH, heq, hseed, hstable, ?_⟩
  intro ρ N
  have hp := polynomial_point_le_scaled_forcing_tail (mul_pos hb.1 sigma_pos) hs₀
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ F * B * ρ ^ 6 by positivity)
  calc
    _ ≤ F * B * ρ ^ 6 * (1 + s₀) ^ 4 := hfinite hs₀ hB N
    _ ≤ Real.exp (b * sigma * s₀) *
        ((F * B * Real.exp (b * sigma)) * ρ ^ 6 * polynomialForcingTail (b * sigma) s₀) :=
      hm.trans_eq (by ring)
    _ ≤ _ := htail ρ

end CircularMaterialTransferProfile
end Euler2D

end
