module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Complex.Exponential

/-! Perturbation bounds using actual bounds for the unperturbed
two-sided evolution, rather than the norm of its possibly large generator. -/

@[expose] public section

noncomputable section

open Set Filter Topology NormedSpace

namespace Euler2D

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

def relativeBanachExponential (a b : A) (t : ℝ) : A :=
  exp ((-t) • a) * exp (t • (a + b))

theorem hasDerivAt_relativeBanachExponential (a b : A) (t : ℝ) :
    HasDerivAt (relativeBanachExponential a b)
      (exp ((-t) • a) * b * exp (t • (a + b))) t := by
  have hn := (hasDerivAt_exp_smul_const a (-t)).scomp t ((hasDerivAt_id t).neg)
  have hp := hasDerivAt_exp_smul_const' (a + b) t
  have h := hn.mul hp
  convert h using 1 <;>
    (try funext s) <;>
    (try dsimp only [relativeBanachExponential, Function.comp_apply, Pi.mul_apply]) <;>
    (try simp only [neg_one_smul]) <;> noncomm_ring

theorem banachExponential_mul_relative (a b : A) (t : ℝ) :
    exp (t • a) * relativeBanachExponential a b t = exp (t • (a + b)) := by
  unfold relativeBanachExponential
  have hprod : exp (t • a) * exp (-(t • a)) = 1 := by
    rw [← exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (Commute.refl (t • a)).neg_right
      ((expSeries_radius_eq_top ℝ A).symm ▸ edist_lt_top _ _)
      ((expSeries_radius_eq_top ℝ A).symm ▸ edist_lt_top _ _), add_neg_cancel, exp_zero]
  rw [neg_smul, ← mul_assoc, hprod, one_mul]

set_option maxHeartbeats 600000 in
theorem norm_banachExponential_perturbation_le (a b : A) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, ‖exp (t • a)‖ ≤ M)
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ‖exp ((-t) • a)‖ ≤ M) :
    ‖exp (T • (a + b)) - exp (T • a)‖ ≤
      M * (Real.exp ((M ^ 2 * ‖b‖) * T) - 1) := by
  let W := relativeBanachExponential a b
  let K := M ^ 2 * ‖b‖
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg M) (norm_nonneg b)
  have hc : Continuous (fun t => W t - 1) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hasDerivAt_relativeBanachExponential a b t).sub_const 1).continuousAt
  have hd (t : ℝ) : HasDerivAt (fun s => W s - 1)
      (exp ((-t) • a) * b * exp (t • (a + b))) t :=
    (hasDerivAt_relativeBanachExponential a b t).sub_const 1
  have hn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖exp ((-t) • a) * b * exp (t • (a + b))‖ ≤ K * ‖W t - 1‖ + K := by
    have he : exp ((-t) • a) * b * exp (t • (a + b)) =
        (exp ((-t) • a) * b * exp (t • a)) * W t := by
      rw [mul_assoc, mul_assoc, banachExponential_mul_relative]
      exact (mul_assoc _ _ _).symm
    have hsmall : ‖exp ((-t) • a) * b * exp (t • a)‖ ≤ K := by
      calc
        _ ≤ ‖exp ((-t) • a)‖ * ‖b‖ * ‖exp (t • a)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ M * ‖b‖ * M := by gcongr <;> first | exact hb t ht | exact hf t ht
        _ = K := by dsimp [K]; ring
    have hW : ‖W t‖ ≤ ‖W t - 1‖ + 1 := by
      simpa only [norm_one, sub_add_cancel] using norm_add_le (W t - 1) (1 : A)
    rw [he]
    calc
      _ ≤ ‖exp ((-t) • a) * b * exp (t • a)‖ * ‖W t‖ := norm_mul_le _ _
      _ ≤ K * (‖W t - 1‖ + 1) := mul_le_mul hsmall hW (norm_nonneg _) hK
      _ = _ := by ring
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hc.continuousOn
    (fun t _ => (hd t).hasDerivWithinAt) (a := (0 : ℝ)) (b := T) (δ := 0) (K := K) (ε := K)
    (by simp only [W, relativeBanachExponential, neg_zero, zero_smul, exp_zero, one_mul,
      sub_self, norm_zero, le_refl])
    (fun t ht => hn t ⟨ht.1, ht.2.le⟩) T ⟨hT, le_rfl⟩
  have hgr : gronwallBound 0 K K T = Real.exp (K * T) - 1 := by
    by_cases hk : K = 0
    · simp only [hk, gronwallBound_K0, zero_add, zero_mul, Real.exp_zero, sub_self]
    · rw [gronwallBound_of_K_ne_0 hk]
      simp only [zero_mul, zero_add, div_self hk, one_mul]
  rw [sub_zero, hgr] at hg
  have he : exp (T • (a + b)) - exp (T • a) = exp (T • a) * (W T - 1) := by
    rw [mul_sub, banachExponential_mul_relative, mul_one]
  rw [he]
  exact (norm_mul_le _ _).trans (mul_le_mul (hf T ⟨hT, le_rfl⟩) hg (norm_nonneg _) hM)

theorem norm_banachExponential_perturbation_le_small (a b : A) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, ‖exp (t • a)‖ ≤ M)
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ‖exp ((-t) • a)‖ ≤ M)
    (hsmall : M ^ 2 * ‖b‖ * T ≤ 1) :
    ‖exp (T • (a + b)) - exp (T • a)‖ ≤ 2 * M ^ 3 * T * ‖b‖ := by
  have hx : 0 ≤ M ^ 2 * ‖b‖ * T := by positivity
  have h := Real.abs_exp_sub_one_le (x := M ^ 2 * ‖b‖ * T)
    (by rw [abs_of_nonneg hx]; exact hsmall)
  have he : Real.exp (M ^ 2 * ‖b‖ * T) - 1 ≤ 2 * (M ^ 2 * ‖b‖ * T) :=
    (le_abs_self _).trans (by simpa only [abs_of_nonneg hx] using h)
  calc
    _ ≤ M * (Real.exp ((M ^ 2 * ‖b‖) * T) - 1) :=
      norm_banachExponential_perturbation_le a b hM hT hf hb
    _ ≤ M * (2 * (M ^ 2 * ‖b‖ * T)) := mul_le_mul_of_nonneg_left he hM
    _ = _ := by ring

end Euler2D

end
