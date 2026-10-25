module

public import RequestProject.Euler.CircularCapturePhysicalScaleBudget
public import RequestProject.Euler.CircularFiniteEulerUniformVectorCorrection
public import RequestProject.Euler.CircularFiniteInnerStageConfinement
public import RequestProject.Euler.CircularWeightedNormParameters

/-! Actual radial and propagation coefficients with R=rho^10 and a
linearly growing support radius. Logarithmic capture windows are kept
throughout, and the already selected nonzero transfer ratio is retained. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Set Filter Topology Polynomial

namespace Euler2D

theorem tendsto_circularCapture_log_monomial (K L D₀ : ℝ) (m n : ℕ) (hm : m ≠ 0) :
    Tendsto (fun ξ : ℝ => K * Real.exp (-ξ) ^ m * (1 + L * ξ + D₀) ^ n)
      atTop (𝓝 0) := by
  let p : ℝ[X] := Polynomial.C K * (1 + (Polynomial.C L * X + Polynomial.C D₀)) ^ n
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hp (ξ : ℝ) : p.eval ξ = K * (1 + L * ξ + D₀) ^ n := by
    simp only [p, eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X]
    ring
  convert tendsto_polynomial_mul_exp_decay p hmR using 1
  ext ξ
  have he : Real.exp (-ξ) ^ m = Real.exp (-(m : ℝ) * ξ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hp, ← he]
  ring

theorem eventually_circularCapture_log_monomial_small
    {K L D₀ ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) (m n : ℕ) (hm : m ≠ 0) :
    ∀ᶠ ξ : ℝ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ L * ξ + D₀ →
      K * Real.exp (-ξ) ^ m * (1 + D) ^ n ≤ ε := by
  have ht := tendsto_circularCapture_log_monomial K L D₀ m n hm
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with ξ hξ
  intro D hD hDlog
  have hpowers : (1 + D) ^ n ≤ (1 + L * ξ + D₀) ^ n := by
    apply pow_le_pow_left₀ (by linarith only [hD])
    linarith only [hDlog]
  exact (mul_le_mul_of_nonneg_left hpowers
    (mul_nonneg hK (pow_nonneg (Real.exp_pos _).le m))).trans hξ.le

theorem tendsto_circularFinite_radialCoefficient_power_scale
    (K b core d₀ d₁ δ : ℝ) (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun ξ : ℝ => finiteEulerUniformRadialCoefficient K b
      (Real.exp (-ξ) ^ m) (Real.exp (-ξ)) core (d₀ + d₁ * ξ) δ)
      atTop (𝓝 ((32 / (15 * core ^ 4) * circularRadialPerturbationWeight) * δ)) := by
  have hden : Tendsto (fun ξ : ℝ => 1 - b * Real.exp (-ξ) ^ 2) atTop (𝓝 1) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
        ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).const_mul b)
  let p : ℝ[X] := Polynomial.C K * (Polynomial.C d₀ + Polynomial.C d₁ * X) ^ 4
  have hrate : (0 : ℝ) < (m * 8 : ℕ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (Nat.pos_of_ne_zero hm) (by decide))
  have hpoly : Tendsto (fun ξ : ℝ => K * (d₀ + d₁ * ξ) ^ 4 *
      (Real.exp (-ξ) ^ m) ^ 8) atTop (𝓝 0) := by
    convert tendsto_polynomial_mul_exp_decay p hrate using 1
    ext ξ
    have he : (Real.exp (-ξ) ^ m) ^ 8 = Real.exp (-((m * 8 : ℕ) : ℝ) * ξ) := by
      rw [← pow_mul, ← Real.exp_nat_mul]
      congr 1
      ring
    simp only [p, eval_mul, eval_C, eval_pow, eval_add, eval_X, he]
  have hsecond := hpoly.mul (tendsto_circularFiniteL1Coefficient_exp_neg b)
  have hfirst := (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => (32 / (15 * core ^ 4) * circularRadialPerturbationWeight) * δ)
    atTop (𝓝 ((32 / (15 * core ^ 4) * circularRadialPerturbationWeight) * δ))).div hden
      (by norm_num : (1 : ℝ) ≠ 0)
  have hsum := hfirst.add hsecond
  convert hsum using 1
  · ext ξ
    simp only [Pi.div_apply]
    unfold finiteEulerUniformRadialCoefficient
    ring
  · simp only [div_one, zero_mul, add_zero]

theorem tendsto_circularFinite_radialCoefficient_coupled_scale
    (K b core d₀ d₁ δ : ℝ) :
    Tendsto (fun ξ : ℝ => finiteEulerUniformRadialCoefficient K b
      (Real.exp (-ξ) ^ 10) (Real.exp (-ξ)) core (d₀ + d₁ * ξ) δ)
      atTop (𝓝 ((32 / (15 * core ^ 4) * circularRadialPerturbationWeight) * δ)) :=
  tendsto_circularFinite_radialCoefficient_power_scale K b core d₀ d₁ δ 10 (by decide)

theorem eventually_circularCapture_log_radial_cubic_budget
    {K b core d₀ d₁ δ Cb Cr L D₀ : ℝ} (hCr : 0 < Cr) :
    ∀ᶠ ξ : ℝ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ L * ξ + D₀ →
      b * finiteEulerUniformRadialCoefficient K b (Real.exp (-ξ) ^ 10)
        (Real.exp (-ξ)) core (d₀ + d₁ * ξ) δ * Cb ^ 3 *
        Real.exp (-ξ) ^ 2 * (1 + D) ^ 3 ≤ Cr / 2 := by
  have hraw := tendsto_circularFinite_radialCoefficient_coupled_scale K b core d₀ d₁ δ
  have hcoef := (hraw.const_mul b).mul_const (Cb ^ 3)
  have habs := hcoef.abs
  have hmono := tendsto_circularCapture_log_monomial 1 L D₀ 2 3 (by decide)
  have ht := habs.mul hmono
  have htzero : Tendsto (fun ξ : ℝ =>
      |b * finiteEulerUniformRadialCoefficient K b (Real.exp (-ξ) ^ 10)
        (Real.exp (-ξ)) core (d₀ + d₁ * ξ) δ * Cb ^ 3| *
        Real.exp (-ξ) ^ 2 * (1 + L * ξ + D₀) ^ 3) atTop (𝓝 0) := by
    simpa only [one_mul, mul_zero, mul_assoc] using ht
  filter_upwards [htzero.eventually (gt_mem_nhds (half_pos hCr))] with ξ hξ
  intro D hD hDlog
  have hpowers : (1 + D) ^ 3 ≤ (1 + L * ξ + D₀) ^ 3 := by
    apply pow_le_pow_left₀ (by linarith only [hD])
    linarith only [hDlog]
  calc
    _ ≤ |b * finiteEulerUniformRadialCoefficient K b (Real.exp (-ξ) ^ 10)
          (Real.exp (-ξ)) core (d₀ + d₁ * ξ) δ * Cb ^ 3| *
        Real.exp (-ξ) ^ 2 * (1 + D) ^ 3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) (by positivity)
    _ ≤ _ := (mul_le_mul_of_nonneg_left hpowers (by positivity)).trans hξ.le

theorem eventually_circularCapture_selected_ratio_gap
    {K b Cup Cdown C₀ Ctorus : ℝ}
    (hb : 0 < b) (hup : 0 ≤ Cup) (hdown : 0 ≤ Cdown) (hC₀ : 1 < C₀)
    (htorus : 0 ≤ Ctorus)
    (hbase : b * K + b * (Cup / (C₀ - 1)) < sigma / 4) :
    ∀ᶠ ξ : ℝ in atTop,
      C₀ * Real.exp (-ξ) ^ 8 < 1 ∧
      ∀ R : ℝ, 0 ≤ R → R ≤ Real.exp (-ξ) →
        b * K ≤ weightedNormPropagationExponent K b Cup Cdown C₀ Ctorus R (Real.exp (-ξ)) ∧
        weightedNormPropagationExponent K b Cup Cdown C₀ Ctorus R (Real.exp (-ξ)) ≤ sigma / 3 := by
  have hlim := tendsto_weightedNormPropagationExponent_diag K b Cup Cdown C₀ Ctorus
  have hexp := hlim.eventually (gt_mem_nhds (show
      b * K + b * (Cup / (C₀ - 1)) < sigma / 3 by linarith only [hbase, sigma_pos]))
  have hζlim : Tendsto (fun ξ : ℝ => C₀ * Real.exp (-ξ) ^ 8) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (8 : ℕ) ≠ 0), mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.pow 8).const_mul C₀
  filter_upwards [hexp, hζlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with ξ hξ hζ
  refine ⟨hζ, ?_⟩
  intro R hR hRρ
  have hfb := weightedInteractionRowFeedback_nonneg hb.le hup hdown hC₀ hζ
  constructor
  · unfold weightedNormPropagationExponent
    have hh : 0 ≤ Ctorus * R ^ 8 := mul_nonneg htorus (pow_nonneg hR 8)
    linarith only [hfb, hh]
  · apply le_trans ?_ hξ.le
    unfold weightedNormPropagationExponent
    exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hR hRρ 8) htorus)) le_rfl

end Euler2D

end
