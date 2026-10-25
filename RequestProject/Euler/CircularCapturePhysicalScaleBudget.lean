module

public import RequestProject.Euler.CircularLogCaptureErrorBudget
public import RequestProject.Euler.InnerCluster

/-! A legal scale-dependent amplitude for logarithmic capture clocks.
The physical radius is the original rho^10 choice. The global support
radius grows only linearly in the logarithmic scale, and all time
bounds hold uniformly in the active finite layer. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Filter Topology Polynomial

namespace Euler2D

theorem exists_eventually_circularCapture_physical_scale_budget
    {T b a Cgeo Lclock Dclock Lnorm Znorm η : ℝ}
    (hT : 0 < T) (hb : 0 < b) (hb1 : b ≤ 1) (ha : 0 < a)
    (hCgeo : 0 < Cgeo) (hLclock : 0 ≤ Lclock) (hDclock : 0 ≤ Dclock)
    (hLnorm : 0 ≤ Lnorm) (hZnorm : 0 ≤ Znorm) (hη : 0 ≤ η) :
    ∃ cA > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let R := ρ ^ 10
      let A₀ := cA * (1 + ξ)
      let d := 2 + 4 * Cgeo * A₀ * T
      0 ≤ ξ ∧ 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ b / 2 ∧
      0 < R ∧ R ≤ ρ ∧ R ≤ 1 / 2 ∧ 0 < A₀ ∧ 0 < d ∧
      5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d ∧
      d * R ≤ 1 / 16 ∧ d * R ≤ a ∧ (5 / 4 : ℝ) * R < a ∧
      (Lnorm + 1) * R ≤ a / 2 ∧ R * (Znorm + η) < a / 4 ∧
      ∀ Dnorm : ℝ, 0 ≤ Dnorm → Dnorm ≤ Lclock * ξ + Dclock →
        ∀ k : ℕ, Dnorm / ampScale A₀ b k < T / 2 := by
  let Cclock := Lclock + Dclock + 1
  have hCclock : 0 < Cclock := by dsimp only [Cclock]; positivity
  let cA := 4 * Cclock / T
  have hcA : 0 < cA := div_pos (mul_pos (by norm_num) hCclock) hT
  have hρlim : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hRlim : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (10 : ℕ) ≠ 0)] using hρlim.pow 10
  let p : ℝ[X] := Polynomial.C 2 + Polynomial.C (4 * Cgeo * cA * T) * (1 + X)
  have hdRlim : Tendsto (fun ξ : ℝ =>
      (2 + 4 * Cgeo * (cA * (1 + ξ)) * T) * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_polynomial_mul_exp_decay p (by norm_num : (0 : ℝ) < 10) using 1
    ext ξ
    have he : Real.exp (-ξ) ^ 10 = Real.exp (-(10 : ℝ) * ξ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [p, eval_add, eval_C, eval_mul, eval_one, eval_X, he]
    ring
  have hρ1 : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ 1 :=
    (hρlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
  have hρb : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ b / 2 :=
    (hρlim.eventually (gt_mem_nhds (half_pos hb))).mono (fun _ h => h.le)
  have hRmax : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ^ 10 ≤ 1 / 2 :=
    (hRlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  have hdR16 : ∀ᶠ ξ : ℝ in atTop,
      (2 + 4 * Cgeo * (cA * (1 + ξ)) * T) * Real.exp (-ξ) ^ 10 ≤ 1 / 16 :=
    (hdRlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))).mono (fun _ h => h.le)
  have hdRa : ∀ᶠ ξ : ℝ in atTop,
      (2 + 4 * Cgeo * (cA * (1 + ξ)) * T) * Real.exp (-ξ) ^ 10 ≤ a :=
    (hdRlim.eventually (gt_mem_nhds ha)).mono (fun _ h => h.le)
  have hRchart : ∀ᶠ ξ : ℝ in atTop, (5 / 4 : ℝ) * Real.exp (-ξ) ^ 10 < a := by
    have ht : Tendsto (fun ξ : ℝ => (5 / 4 : ℝ) * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
      simpa only [mul_zero] using hRlim.const_mul (5 / 4 : ℝ)
    exact ht.eventually (gt_mem_nhds ha)
  have hgeom : ∀ᶠ ξ : ℝ in atTop, (Lnorm + 1) * Real.exp (-ξ) ^ 10 ≤ a / 2 := by
    have ht : Tendsto (fun ξ : ℝ => (Lnorm + 1) * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
      simpa only [mul_zero] using hRlim.const_mul (Lnorm + 1)
    exact (ht.eventually (gt_mem_nhds (half_pos ha))).mono (fun _ h => h.le)
  have hsize : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ^ 10 * (Znorm + η) < a / 4 := by
    have ht : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 10 * (Znorm + η)) atTop (𝓝 0) := by
      simpa only [zero_mul] using hRlim.mul_const (Znorm + η)
    exact ht.eventually (gt_mem_nhds (div_pos ha (by norm_num)))
  refine ⟨cA, hcA, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ), hρ1, hρb, hRmax, hdR16, hdRa,
    hRchart, hgeom, hsize] with ξ hξ hρone hρhalf hRhalf hdRsmall hdRsmallA hRsmall hgeomξ hsizeξ
  dsimp only
  let ρ := Real.exp (-ξ)
  let A₀ := cA * (1 + ξ)
  let d := 2 + 4 * Cgeo * A₀ * T
  have hρpos : 0 < ρ := Real.exp_pos _
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hcat : 0 ≤ Cgeo * A₀ * T := mul_nonneg (mul_nonneg hCgeo.le hA.le) hT.le
  have hd : 0 < d := by dsimp only [d]; nlinarith only [hcat]
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hh : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith only [hρhalf])
    linarith only [hh]
  have hcoef : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hcoef hT.le
    dsimp only [d]
    nlinarith only [hh, hcat]
  have hRrho : ρ ^ 10 ≤ ρ := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hρpos.le hρone (by decide : (1 : ℕ) ≤ 10))
  refine ⟨hξ, hρpos, hρone, hρhalf, pow_pos hρpos _,
    hRrho, hRhalf, hA, hd,
    hdrift, hdRsmall, hdRsmallA, hRsmall, hgeomξ, hsizeξ, ?_⟩
  intro Dnorm hD hDclockBound k
  have hclock : Lclock * ξ + Dclock ≤ Cclock * (1 + ξ) := by
    have hh := mul_nonneg (show 0 ≤ Dclock + 1 by linarith only [hDclock]) hξ
    dsimp only [Cclock]
    nlinarith only [hh, hLclock]
  have htime : Dnorm / A₀ < T / 2 := by
    apply (div_lt_iff₀ hA).mpr
    have hpositive : 0 < Cclock * (1 + ξ) := mul_pos hCclock (by linarith only [hξ])
    have heq : T / 2 * A₀ = 2 * Cclock * (1 + ξ) := by
      dsimp only [A₀, cA]
      field_simp [hT.ne'] <;> ring
    rw [heq]
    linarith only [hDclockBound, hclock, hpositive]
  have hAkLower : A₀ ≤ ampScale A₀ b k := by
    unfold ampScale
    apply (le_div_iff₀ (pow_pos hb k)).mpr
    exact mul_le_of_le_one_right hA.le (pow_le_one₀ hb.le hb1)
  exact (div_le_div_of_nonneg_left hD hA hAkLower).trans_lt htime

end Euler2D

end
