module

public import RequestProject.Euler.CircularCaptureCoupledScaleSmallness
public import RequestProject.Euler.CircularCaptureCascadeClockBudget

/-! A genuine logarithmic-clock absorption estimate. These pointwise
inequalities are intended for the norm of the SAME actual material contour.
They do not assert an Euler history until that actual substitution is proved. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

open Set Filter Topology Polynomial

namespace Euler2D

theorem eventually_circularCapture_early_past_slow_absorption
    {rate Lclock Dclock K η : ℝ}
    (hrate : 0 ≤ rate) (hK : 0 ≤ K) (hη : 0 < η) (hgap : rate * Lclock < 6) :
    ∀ᶠ ξ : ℝ in atTop,
      ∀ exit t : ℝ, exit ≤ Lclock * ξ + Dclock → 0 ≤ t →
      K * Real.exp (-ξ) ^ 6 ≤ η * Real.exp (-rate * (exit - t)) := by
  have hdecay : 0 < 6 - rate * Lclock := sub_pos.mpr hgap
  have hidentity (ξ : ℝ) :
      K * Real.exp (-ξ) ^ 6 * Real.exp (rate * (Lclock * ξ + Dclock)) =
        (K * Real.exp (rate * Dclock)) * Real.exp (-(6 - rate * Lclock) * ξ) := by
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    congr 1
    ring
  have hlim : Tendsto (fun ξ : ℝ => K * Real.exp (-ξ) ^ 6 *
      Real.exp (rate * (Lclock * ξ + Dclock))) atTop (𝓝 0) := by
    convert tendsto_polynomial_mul_exp_decay
      (Polynomial.C (K * Real.exp (rate * Dclock))) hdecay using 1
    ext ξ
    simpa only [Polynomial.eval_C] using hidentity ξ
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with ξ hξ
  intro exit t hclock ht
  have hexp : Real.exp (rate * (exit - t)) ≤
      Real.exp (rate * (Lclock * ξ + Dclock)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith only [hclock, ht]) hrate)
  have hbound : K * Real.exp (-ξ) ^ 6 * Real.exp (rate * (exit - t)) ≤ η :=
    (mul_le_mul_of_nonneg_left hexp
      (mul_nonneg hK (pow_nonneg (Real.exp_pos _).le 6))).trans hξ.le
  calc
    _ = (K * Real.exp (-ξ) ^ 6 * Real.exp (rate * (exit - t))) *
        Real.exp (-rate * (exit - t)) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le

theorem circularCapture_half_rate_clock_margin {Lclock b : ℝ}
    (hclock : sigma * Lclock < 8) (hb : b < 1 / 4) :
    0 < sigma / 2 ∧ (sigma / 2) * Lclock < 6 ∧ b * sigma < sigma / 2 := by
  have hh := mul_lt_mul_of_pos_right hb sigma_pos
  refine ⟨half_pos sigma_pos, ?_, ?_⟩
  · nlinarith only [hclock]
  · nlinarith only [hh, sigma_pos]

theorem circularCapture_splice_slow_past_decay
    {rate η entrance Dcap hit : ℝ} (v : ℝ → ℝ)
    (hrate : 0 ≤ rate) (hfast : rate ≤ sigma) (hη : 0 ≤ η)
    (hentrance : 0 ≤ entrance) (hhit : hit ∈ Icc (0 : ℝ) Dcap)
    (hearly : ∀ t ∈ Icc (0 : ℝ) entrance,
      v t ≤ η * Real.exp (-rate * ((entrance + hit) - t)))
    (hcapture : ∀ u ∈ Icc (0 : ℝ) Dcap,
      v (entrance + u) ≤ η * Real.exp (-sigma * (Dcap - u))) :
    ∀ t ∈ Icc (0 : ℝ) (entrance + hit),
      v t ≤ η * Real.exp (-rate * ((entrance + hit) - t)) := by
  intro t ht
  by_cases he : t ≤ entrance
  · exact hearly t ⟨ht.1, he⟩
  · let u := t - entrance
    have hu0 : 0 ≤ u := by dsimp only [u]; linarith only [he]
    have huh : u ≤ hit := by dsimp only [u]; linarith only [ht.2]
    have huD : u ≤ Dcap := huh.trans hhit.2
    have hremaining : 0 ≤ Dcap - u := sub_nonneg.mpr huD
    have hcompare : rate * (hit - u) ≤ sigma * (Dcap - u) :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hhit.2 u) hrate).trans
        (mul_le_mul_of_nonneg_right hfast hremaining)
    have hclock : (entrance + hit) - t = hit - u := by dsimp only [u]; ring
    have hexp : Real.exp (-sigma * (Dcap - u)) ≤
        Real.exp (-rate * ((entrance + hit) - t)) := by
      apply Real.exp_le_exp.mpr
      rw [hclock]
      linarith only [hcompare]
    have hcap : v t ≤ η * Real.exp (-sigma * (Dcap - u)) := by
      have hh := hcapture u ⟨hu0, huD⟩
      have heq : entrance + u = t := by dsimp only [u]; ring
      rwa [heq] at hh
    exact hcap.trans (mul_le_mul_of_nonneg_left hexp hη)

theorem eventually_circularCapture_whole_past_slow_decay
    {rate Lclock Dclock K η : ℝ}
    (hrate : 0 ≤ rate) (hfast : rate ≤ sigma)
    (hK : 0 ≤ K) (hη : 0 < η) (hgap : rate * Lclock < 6) :
    ∀ᶠ ξ : ℝ in atTop,
      ∀ entrance Dcap hit : ℝ, ∀ v : ℝ → ℝ,
      0 ≤ entrance → hit ∈ Icc (0 : ℝ) Dcap → entrance + hit ≤ Lclock * ξ + Dclock →
      (∀ t ∈ Icc (0 : ℝ) entrance, v t ≤ K * Real.exp (-ξ) ^ 6) →
      (∀ u ∈ Icc (0 : ℝ) Dcap,
        v (entrance + u) ≤ η * Real.exp (-sigma * (Dcap - u))) →
      ∀ t ∈ Icc (0 : ℝ) (entrance + hit),
        v t ≤ η * Real.exp (-rate * ((entrance + hit) - t)) := by
  filter_upwards [eventually_circularCapture_early_past_slow_absorption hrate hK hη hgap]
    with ξ habsorb
  intro entrance Dcap hit v he hhit hclock hpast hcap
  apply circularCapture_splice_slow_past_decay v hrate hfast hη.le he hhit
  · intro t ht
    exact (hpast t ht).trans (habsorb (entrance + hit) t hclock ht.1)
  · exact hcap

end Euler2D

end
