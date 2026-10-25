module

public import Mathlib
public import RequestProject.Euler.MomentVariation

/-!
# Support of a contour perturbation (Lemma `ib:lem:annular`)

A near-circular two-interface label has interfaces that are radial graphs
`D_j = {z : |z| < R_j(arg z)}` (`starDomain`), and its circular reference has the disks
`B_{d_j r}`. With amplitude `A` and interface jumps `g_j` the perturbation is
`η = A Σ_j g_j (1_{D_j} − 1_{B_{d_j r}})` (`annularPerturbation`).

* `area_starDomain`: `|D_R| = ∫_{−π}^{π} R(θ)²/2 dθ`.
* `integral_abs_starInd_sub`: `‖1_{D_R} − 1_{B_ρ}‖₁ = ∫_{−π}^{π} |R² − ρ²|/2 dθ`.
* `annular_perturbation`: if `c r ≤ R_j ≤ C r`, `c ≤ d_j ≤ C`, `|R_j − d_j r| ≤ r q`,
  `|D_j| = π (d_j r)²` and `R_j` is `2π`-periodic and invariant under `θ ↦ θ + π/2`, then
  `η = 0` in `B_{cr}`, `η = 0` outside `B_{Cr}`, `‖η‖₁ ≤ π|A|(|g₁|(2d₁+q) + |g₂|(2d₂+q)) r² q`,
  `∫ η = 0` and `η(iz) = η(z)`.

The paper allows interfaces that become radial graphs only after reparametrization; here the
radial-graph form is assumed directly.
-/

@[expose] public section

open MeasureTheory Complex Set Real Metric

namespace Euler2D

/-- The indicator `1_{D_R}` of the star-shaped domain with radial function `R`. -/
noncomputable def starInd (R : ℝ → ℝ) (z : ℂ) : ℝ := (starDomain R).indicator 1 z

/-- The perturbation `η = A Σ_j g_j (1_{D_j} − 1_{B_{ρ_j}})` of a two-interface label. -/
noncomputable def annularPerturbation (A g₁ g₂ : ℝ) (R₁ R₂ : ℝ → ℝ) (ρ₁ ρ₂ : ℝ) (z : ℂ) : ℝ :=
  A * (g₁ * (starInd R₁ z - starInd (fun _ => ρ₁) z) + g₂ * (starInd R₂ z - starInd (fun _ => ρ₂) z))

lemma measurableSet_starDomain {R : ℝ → ℝ} (hR : Continuous R) : MeasurableSet (starDomain R) :=
  measurableSet_lt measurable_norm (hR.measurable.comp Complex.measurable_arg)

lemma starDomain_subset_ball {R : ℝ → ℝ} {C : ℝ} (hC : ∀ θ, R θ ≤ C) :
    starDomain R ⊆ ball 0 C := by
  intro z hz
  rw [mem_ball_zero_iff]
  exact lt_of_lt_of_le hz (hC _)

lemma volReal_Ioo_pi : volume.real (Ioo (-π) π) = 2 * π := by
  rw [Real.volume_real_Ioo_of_le (by linarith [pi_pos])]; ring

lemma starInd_of_lt {R : ℝ → ℝ} {z : ℂ} (h : ‖z‖ < R (arg z)) : starInd R z = 1 := by
  simp [starInd, starDomain, indicator, h]

lemma starInd_of_le {R : ℝ → ℝ} {z : ℂ} (h : R (arg z) ≤ ‖z‖) : starInd R z = 0 := by
  simp [starInd, starDomain, indicator, not_lt.mpr h]

lemma integrable_starInd {R : ℝ → ℝ} (hR : Continuous R) {C : ℝ} (hC : ∀ θ, R θ ≤ C) :
    Integrable (starInd R) := by
  unfold starInd
  rw [integrable_indicator_iff (measurableSet_starDomain hR)]
  exact (integrableOn_const (C := (1 : ℝ)) measure_ball_lt_top.ne enorm_ne_top).mono_set
    (starDomain_subset_ball hC)

lemma integral_starInd {R : ℝ → ℝ} (hR : Continuous R) :
    ∫ z, starInd R z = volume.real (starDomain R) :=
  integral_indicator_one (measurableSet_starDomain hR)

/-- Area of a star-shaped domain in polar coordinates. -/
theorem area_starDomain {R : ℝ → ℝ} (hR : Continuous R) (hpos : ∀ θ, 0 < R θ) :
    volume.real (starDomain R) = ∫ θ in Ioo (-π) π, R θ ^ 2 / 2 := by
  have h := momentJ_starDomain hR hpos 0
  simp only [momentJ, pow_zero, setIntegral_const, CharP.cast_eq_zero, zero_mul, neg_zero,
    Complex.exp_zero, one_mul, zero_add] at h
  rw [integral_complex_ofReal] at h
  have h2 : ((volume.real (starDomain R) : ℝ) : ℂ) = ((∫ θ in Ioo (-π) π, R θ ^ 2 / 2 : ℝ) : ℂ) := by
    rw [← h]; simp
  exact_mod_cast h2

/-- `‖1_{D_R} − 1_{B_ρ}‖₁ = ∫_{−π}^{π} |R² − ρ²|/2 dθ`. -/
theorem integral_abs_starInd_sub {R : ℝ → ℝ} (hR : Continuous R) (hpos : ∀ θ, 0 < R θ)
    {C : ℝ} (hC : ∀ θ, R θ ≤ C) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ z, |starInd R z - starInd (fun _ => ρ) z| = ∫ θ in Ioo (-π) π, |R θ ^ 2 - ρ ^ 2| / 2 := by
  have hpt : ∀ z, |starInd R z - starInd (fun _ => ρ) z| =
      starInd (fun θ => max (R θ) ρ) z - starInd (fun θ => min (R θ) ρ) z := by
    intro z
    by_cases h1 : ‖z‖ < R (arg z) <;> by_cases h2 : ‖z‖ < ρ <;>
      simp [starInd, starDomain, indicator, h1, h2]
  have hmaxc : Continuous fun θ => max (R θ) ρ := hR.max continuous_const
  have hminc : Continuous fun θ => min (R θ) ρ := hR.min continuous_const
  have hCρ : ∀ θ, max (R θ) ρ ≤ max C ρ := fun θ => max_le_max (hC θ) le_rfl
  have hCρ' : ∀ θ, min (R θ) ρ ≤ C := fun θ => (min_le_left _ _).trans (hC θ)
  simp_rw [hpt]
  rw [integral_sub (integrable_starInd hmaxc hCρ) (integrable_starInd hminc hCρ'),
    integral_starInd hmaxc, integral_starInd hminc,
    area_starDomain hmaxc (fun θ => lt_max_of_lt_right hρ),
    area_starDomain hminc (fun θ => lt_min (hpos θ) hρ), ← integral_sub]
  · refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    have h0 := hpos θ
    rcases le_total (R θ) ρ with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by nlinarith)]; ring
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by nlinarith)]; ring
  · exact ((hmaxc.pow 2).div_const 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact ((hminc.pow 2).div_const 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- The `L¹` bound for one interface: `|R − ρ| ≤ δ` gives `‖1_{D_R} − 1_{B_ρ}‖₁ ≤ π δ (2ρ + δ)`. -/
theorem integral_abs_starInd_sub_le {R : ℝ → ℝ} (hR : Continuous R) (hpos : ∀ θ, 0 < R θ)
    {C : ℝ} (hC : ∀ θ, R θ ≤ C) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : ∀ θ, |R θ - ρ| ≤ δ) :
    ∫ z, |starInd R z - starInd (fun _ => ρ) z| ≤ π * δ * (2 * ρ + δ) := by
  rw [integral_abs_starInd_sub hR hpos hC hρ]
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  calc ∫ θ in Ioo (-π) π, |R θ ^ 2 - ρ ^ 2| / 2
      ≤ ∫ θ in Ioo (-π) π, δ * (2 * ρ + δ) / 2 := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo fun θ _ => ?_
        · exact (((hR.pow 2).sub continuous_const).abs.div_const 2).integrableOn_Icc.mono_set
            Ioo_subset_Icc_self
        · exact integrableOn_const (by simp) enorm_ne_top
        · have h1 := hδ θ
          have h0 := hpos θ
          rw [show R θ ^ 2 - ρ ^ 2 = (R θ - ρ) * (R θ + ρ) by ring, abs_mul,
            abs_of_pos (by linarith : 0 < R θ + ρ)]
          have h2 : R θ + ρ ≤ 2 * ρ + δ := by linarith [le_abs_self (R θ - ρ)]
          have := mul_le_mul h1 h2 (by linarith) hδ0
          linarith
    _ = π * δ * (2 * ρ + δ) := by
        rw [setIntegral_const, volReal_Ioo_pi, smul_eq_mul]; ring

/-- Equal areas give zero mass for one interface. -/
theorem integral_starInd_sub {R : ℝ → ℝ} (hR : Continuous R)
    {C : ℝ} (hC : ∀ θ, R θ ≤ C) {ρ : ℝ} (hρ : 0 < ρ)
    (harea : volume.real (starDomain R) = π * ρ ^ 2) :
    ∫ z, (starInd R z - starInd (fun _ => ρ) z) = 0 := by
  have hc : Continuous fun _ : ℝ => ρ := continuous_const
  rw [integral_sub (integrable_starInd hR hC) (integrable_starInd hc (fun _ => le_rfl)),
    integral_starInd hR, integral_starInd hc, harea,
    area_starDomain hc (fun _ => hρ), setIntegral_const, volReal_Ioo_pi, smul_eq_mul]
  ring

/-- Quarter-turn invariance of a star-shaped domain with a quarter-periodic radial function. -/
theorem starInd_rot {R : ℝ → ℝ} (hper : Function.Periodic R (2 * π))
    (hrot : ∀ θ, R (θ + π / 2) = R θ) (z : ℂ) : starInd R (I * z) = starInd R z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have harg : R (arg (I * z)) = R (arg z) := by
    have h := Complex.arg_mul_coe_angle I_ne_zero hz
    rw [Complex.arg_I, ← Real.Angle.coe_add] at h
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
    rw [show arg (I * z) = (arg z + π / 2) + k * (2 * π) by linarith, (hper.int_mul k) _,
      add_comm (arg z), ← hrot (arg z), add_comm]
  simp only [starInd, starDomain, indicator, mem_setOf_eq, norm_mul, Complex.norm_I, one_mul,
    harg, Pi.one_apply]

/-- **Lemma `ib:lem:annular`.** -/
theorem annular_perturbation {A g₁ g₂ r q c C d₁ d₂ : ℝ} {R₁ R₂ : ℝ → ℝ}
    (hr : 0 < r) (hc : 0 < c) (hR₁ : Continuous R₁) (hR₂ : Continuous R₂)
    (hlo₁ : ∀ θ, c * r ≤ R₁ θ) (hlo₂ : ∀ θ, c * r ≤ R₂ θ)
    (hhi₁ : ∀ θ, R₁ θ ≤ C * r) (hhi₂ : ∀ θ, R₂ θ ≤ C * r)
    (hd₁ : c ≤ d₁) (hd₂ : c ≤ d₂) (hd₁' : d₁ ≤ C) (hd₂' : d₂ ≤ C)
    (hq₁ : ∀ θ, |R₁ θ - d₁ * r| ≤ r * q) (hq₂ : ∀ θ, |R₂ θ - d₂ * r| ≤ r * q)
    (harea₁ : volume.real (starDomain R₁) = π * (d₁ * r) ^ 2)
    (harea₂ : volume.real (starDomain R₂) = π * (d₂ * r) ^ 2)
    (hper₁ : Function.Periodic R₁ (2 * π)) (hper₂ : Function.Periodic R₂ (2 * π))
    (hrot₁ : ∀ θ, R₁ (θ + π / 2) = R₁ θ) (hrot₂ : ∀ θ, R₂ (θ + π / 2) = R₂ θ) :
    let η := annularPerturbation A g₁ g₂ R₁ R₂ (d₁ * r) (d₂ * r)
    (∀ z, ‖z‖ < c * r → η z = 0) ∧ (∀ z, C * r ≤ ‖z‖ → η z = 0) ∧
      Integrable η ∧
      ∫ z, |η z| ≤ π * |A| * (|g₁| * (2 * d₁ + q) + |g₂| * (2 * d₂ + q)) * r ^ 2 * q ∧
      ∫ z, η z = 0 ∧ (∀ z, η (I * z) = η z) := by
  intro η
  have hcr : 0 < c * r := mul_pos hc hr
  have hpos₁ : ∀ θ, 0 < R₁ θ := fun θ => hcr.trans_le (hlo₁ θ)
  have hpos₂ : ∀ θ, 0 < R₂ θ := fun θ => hcr.trans_le (hlo₂ θ)
  have hρ₁ : c * r ≤ d₁ * r := mul_le_mul_of_nonneg_right hd₁ hr.le
  have hρ₂ : c * r ≤ d₂ * r := mul_le_mul_of_nonneg_right hd₂ hr.le
  have hρ₁' : d₁ * r ≤ C * r := mul_le_mul_of_nonneg_right hd₁' hr.le
  have hρ₂' : d₂ * r ≤ C * r := mul_le_mul_of_nonneg_right hd₂' hr.le
  have hi₁ := integrable_starInd hR₁ hhi₁
  have hi₂ := integrable_starInd hR₂ hhi₂
  have hj₁ := integrable_starInd (R := fun _ => d₁ * r) continuous_const (fun _ => hρ₁')
  have hj₂ := integrable_starInd (R := fun _ => d₂ * r) continuous_const (fun _ => hρ₂')
  have hint : Integrable η :=
    (((hi₁.sub hj₁).const_mul g₁).add ((hi₂.sub hj₂).const_mul g₂)).const_mul A
  refine ⟨fun z hz => ?_, fun z hz => ?_, hint, ?_, ?_, fun z => ?_⟩
  · simp only [η, annularPerturbation]
    rw [starInd_of_lt (hz.trans_le (hlo₁ _)), starInd_of_lt (hz.trans_le (hlo₂ _)),
      starInd_of_lt (R := fun _ => d₁ * r) (hz.trans_le hρ₁),
      starInd_of_lt (R := fun _ => d₂ * r) (hz.trans_le hρ₂)]
    ring
  · simp only [η, annularPerturbation]
    rw [starInd_of_le ((hhi₁ _).trans hz), starInd_of_le ((hhi₂ _).trans hz),
      starInd_of_le (R := fun _ => d₁ * r) (hρ₁'.trans hz),
      starInd_of_le (R := fun _ => d₂ * r) (hρ₂'.trans hz)]
    ring
  · have hb₁ := integral_abs_starInd_sub_le hR₁ hpos₁ hhi₁ (hcr.trans_le hρ₁) hq₁
    have hb₂ := integral_abs_starInd_sub_le hR₂ hpos₂ hhi₂ (hcr.trans_le hρ₂) hq₂
    have hle : ∀ z, |η z| ≤ |A| * (|g₁| * |starInd R₁ z - starInd (fun _ => d₁ * r) z| +
        |g₂| * |starInd R₂ z - starInd (fun _ => d₂ * r) z|) := by
      intro z
      simp only [η, annularPerturbation, abs_mul]
      gcongr
      exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
    have hI1 : Integrable (fun z => |g₁| * |starInd R₁ z - starInd (fun _ => d₁ * r) z|) :=
      (hi₁.sub hj₁).abs.const_mul _
    have hI2 : Integrable (fun z => |g₂| * |starInd R₂ z - starInd (fun _ => d₂ * r) z|) :=
      (hi₂.sub hj₂).abs.const_mul _
    calc ∫ z, |η z|
        ≤ ∫ z, |A| * (|g₁| * |starInd R₁ z - starInd (fun _ => d₁ * r) z| +
            |g₂| * |starInd R₂ z - starInd (fun _ => d₂ * r) z|) :=
          integral_mono hint.abs ((hI1.add hI2).const_mul _) hle
      _ = |A| * (|g₁| * (∫ z, |starInd R₁ z - starInd (fun _ => d₁ * r) z|) +
            |g₂| * ∫ z, |starInd R₂ z - starInd (fun _ => d₂ * r) z|) := by
          rw [integral_const_mul, integral_add hI1 hI2, integral_const_mul, integral_const_mul]
      _ ≤ |A| * (|g₁| * (π * (r * q) * (2 * (d₁ * r) + r * q)) +
            |g₂| * (π * (r * q) * (2 * (d₂ * r) + r * q))) := by
          gcongr
      _ = π * |A| * (|g₁| * (2 * d₁ + q) + |g₂| * (2 * d₂ + q)) * r ^ 2 * q := by ring
  · have hJ1 : Integrable (fun z => g₁ * (starInd R₁ z - starInd (fun _ => d₁ * r) z)) :=
      (hi₁.sub hj₁).const_mul _
    have hJ2 : Integrable (fun z => g₂ * (starInd R₂ z - starInd (fun _ => d₂ * r) z)) :=
      (hi₂.sub hj₂).const_mul _
    simp only [η, annularPerturbation]
    rw [integral_const_mul, integral_add hJ1 hJ2,
      integral_const_mul, integral_const_mul,
      integral_starInd_sub hR₁ hhi₁ (hcr.trans_le hρ₁) harea₁,
      integral_starInd_sub hR₂ hhi₂ (hcr.trans_le hρ₂) harea₂]
    ring
  · have hconst : ∀ ρ : ℝ, starInd (fun _ => ρ) (I * z) = starInd (fun _ => ρ) z := fun ρ =>
      starInd_rot (fun _ => rfl) (fun _ => rfl) z
    simp only [η, annularPerturbation, hconst, starInd_rot hper₁ hrot₁, starInd_rot hper₂ hrot₂]

end Euler2D
