module

public import Mathlib
public import RequestProject.Euler.TorusCancellation

/-!
# Periodic correction for outer and inner sources (Corollary `cs:cor:periodic`)

Consequences of Lemma `cs:toruslemma` (`periodic_remainder_cancellation`) for the kernel
`c|z|² + h(z)` with `h` harmonic on `B_{8a}` and invariant under the quarter turn:

* `periodic_correction_sources`: if the fourth absolute moment of a source is at most `B`
  (for an outer perturbation, `B = C δ A_ℓ r_ℓ⁶`), the correction velocity is at most
  `K B |x|³` for `|x| ≤ a`; at points with `|x| ≤ c₁ r` (for an inner cluster, `|x| ≍ r_k`),
  it is at most `K c₁³ r³ M^{abs}_4`. The constant `K` depends only on `h`, `c` and `a`.
* `radial_reference_zero_correction`: a radial zero-mass source has zero periodic correction
  velocity (harmonic mean value property for `h`, zero mass and zero first moment for the
  quadratic part).
-/

@[expose] public section

open MeasureTheory Complex Metric Set Filter

namespace Euler2D

/-- **Corollary `cs:cor:periodic`.** There is `K ≥ 0`, depending only on `h, c, a`, such that
for every integrable, fourfold-symmetric, zero-mass `ζ` supported in `B̄_a` and every `x` with
`|x| ≤ a`: if `∫|y|⁴|ζ| ≤ B` then the correction is at most `K B |x|³` (outer perturbations),
and if `|x| ≤ c₁ r` then it is at most `K c₁³ r³ ∫|y|⁴|ζ|` (inner clusters). -/
theorem periodic_correction_sources {h : ℂ → ℝ} {a : ℝ} (c : ℝ) (ha : 0 < a)
    (hh : InnerProductSpace.HarmonicOnNhd h (ball 0 (8 * a)))
    (hrot : ∀ z ∈ ball (0 : ℂ) (8 * a), h (I * z) = h z) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ : ℂ → ℝ, Integrable ζ → (∀ y, a < ‖y‖ → ζ y = 0) →
      (∀ y, ζ (I * y) = ζ y) → ∫ y, ζ y = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        (∀ B : ℝ, ∫ y, ‖y‖ ^ 4 * |ζ y| ≤ B →
          ‖fderiv ℝ (fun x => ∫ y, (c * ‖x - y‖ ^ 2 + h (x - y)) * ζ y) x‖
            ≤ K * B * ‖x‖ ^ 3) ∧
        (∀ r c₁ : ℝ, ‖x‖ ≤ c₁ * r →
          ‖fderiv ℝ (fun x => ∫ y, (c * ‖x - y‖ ^ 2 + h (x - y)) * ζ y) x‖
            ≤ K * c₁ ^ 3 * r ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y|) := by
  obtain ⟨K, hK⟩ := periodic_remainder_cancellation c ha hh hrot
  refine ⟨max K 0, le_max_right _ _, fun ζ hζ hsupp hsym hmass x hx => ?_⟩
  have hbase := hK ζ hζ hsupp hsym hmass x hx
  have hM : 0 ≤ ∫ y, ‖y‖ ^ 4 * |ζ y| := integral_nonneg (fun y => by positivity)
  have hbase' : ‖fderiv ℝ (fun x => ∫ y, (c * ‖x - y‖ ^ 2 + h (x - y)) * ζ y) x‖ ≤
      max K 0 * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| :=
    hbase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hM)
  refine ⟨fun B hB => hbase'.trans ?_, fun r c₁ hr => hbase'.trans ?_⟩
  · have h0 : 0 ≤ max K 0 * ‖x‖ ^ 3 := mul_nonneg (le_max_right _ _) (by positivity)
    calc max K 0 * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| ≤ max K 0 * ‖x‖ ^ 3 * B :=
          mul_le_mul_of_nonneg_left hB h0
      _ = max K 0 * B * ‖x‖ ^ 3 := by ring
  · have h3 : ‖x‖ ^ 3 ≤ (c₁ * r) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hr 3
    calc max K 0 * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y|
        ≤ max K 0 * (c₁ * r) ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (le_max_right _ _)) hM
      _ = max K 0 * c₁ ^ 3 * r ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by ring

/-- Mean value property in rotated form: `∫₀^{2π} h(x - e^{iθ} y) dθ = 2π h(x)` for `h` harmonic
on a ball containing `B̄(x, |y|)`. -/
lemma circle_mean_rotated {h : ℂ → ℝ} {x y : ℂ} {R : ℝ}
    (hh : InnerProductSpace.HarmonicOnNhd h (ball 0 R)) (hxy : ‖x‖ + ‖y‖ < R) :
    ∫ θ in Ioc 0 (2 * Real.pi), h (x - cexp (θ * I) * y) = 2 * Real.pi * h x := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  set ψ := (-y).arg
  have hrep : ∀ θ : ℝ, x - cexp (θ * I) * y = circleMap x ‖y‖ (θ + ψ) := by
    intro θ
    have h1 := Complex.norm_mul_exp_arg_mul_I (-y)
    rw [norm_neg] at h1
    rw [circleMap]
    have : cexp (((θ + ψ : ℝ) : ℂ) * I) = cexp (θ * I) * cexp (ψ * I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [this]
    calc x - cexp (θ * I) * y = x + cexp (θ * I) * (-y) := by ring
      _ = x + cexp (θ * I) * (‖y‖ * cexp (ψ * I)) := by rw [h1]
      _ = _ := by ring
  simp_rw [hrep]
  rw [intervalIntegral.integral_comp_add_right (fun t => h (circleMap x ‖y‖ t)) ψ]
  have hper : Function.Periodic (fun t => h (circleMap x ‖y‖ t)) (2 * Real.pi) :=
    (periodic_circleMap x ‖y‖).comp h
  rw [zero_add, add_comm (2 * Real.pi) ψ, hper.intervalIntegral_add_eq ψ 0, zero_add]
  have hmv : Real.circleAverage h x ‖y‖ = h x := by
    apply HarmonicOnNhd.circleAverage_eq
    intro z hz
    apply hh
    rw [mem_closedBall, abs_norm] at hz
    rw [mem_ball_zero_iff]
    calc ‖z‖ ≤ ‖x‖ + dist z x := by
          have := norm_sub_norm_le z x; rw [dist_eq_norm]; linarith
      _ < R := by linarith
  rw [Real.circleAverage_def] at hmv
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [← hmv, smul_eq_mul]
  field_simp

/-- Rotations preserve Lebesgue measure on `ℂ`. -/
lemma integral_comp_rotation (g : ℂ → ℝ) (θ : ℝ) :
    ∫ y, g (cexp (θ * I) * y) = ∫ y, g y := by
  have h := (rotation (Circle.exp θ)).measurePreserving.integral_comp
    (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding g
  simpa [rotation_apply, Circle.coe_exp] using h

/-- For a radial, zero-mass `ζ` supported in `B̄_a` and `h` harmonic on `B_{8a}`,
`∫ h(x - y) ζ(y) dy = 0` for `|x| ≤ a` (harmonic mean value property and zero mass). -/
lemma radial_harmonic_conv_zero {h ζ : ℂ → ℝ} {a : ℝ} {x : ℂ} (ha : 0 < a)
    (hh : InnerProductSpace.HarmonicOnNhd h (ball 0 (8 * a))) (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (hrad : ∀ (θ : ℝ) (y : ℂ), ζ (cexp (θ * I) * y) = ζ y)
    (hmass : ∫ y, ζ y = 0) (hx : ‖x‖ ≤ a) :
    ∫ y, h (x - y) * ζ y = 0 := by
  classical
  have hsub3 : closedBall (0 : ℂ) (3 * a) ⊆ ball 0 (8 * a) := closedBall_subset_ball (by linarith)
  have hhc : ContinuousOn h (closedBall 0 (3 * a)) :=
    (fun z hz => (hh z (hsub3 hz)).1.continuousAt.continuousWithinAt)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (3 * a)).exists_bound_of_continuousOn hhc
  set ht : ℂ → ℝ := (closedBall (0 : ℂ) (3 * a)).piecewise h 0 with ht_def
  have htm : Measurable ht :=
    ContinuousOn.measurable_piecewise hhc continuousOn_const measurableSet_closedBall
  have hmem : ∀ (θ : ℝ) (y : ℂ), ‖y‖ ≤ a → x - cexp (θ * I) * y ∈ closedBall (0 : ℂ) (3 * a) := by
    intro θ y hy
    rw [mem_closedBall_zero_iff]
    calc ‖x - cexp (θ * I) * y‖ ≤ ‖x‖ + ‖cexp (θ * I) * y‖ := norm_sub_le _ _
      _ = ‖x‖ + ‖y‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      _ ≤ 3 * a := by linarith
  have heq : ∀ (θ : ℝ) (y : ℂ), ht (x - cexp (θ * I) * y) * ζ y = h (x - cexp (θ * I) * y) * ζ y := by
    intro θ y
    by_cases hy : ‖y‖ ≤ a
    · rw [ht_def, Set.piecewise_eq_of_mem _ _ _ (hmem θ y hy)]
    · rw [hsupp y (not_le.mp hy)]; simp
  have hbt : ∀ z, ‖ht z‖ ≤ B := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) (3 * a)
    · rw [ht_def, Set.piecewise_eq_of_mem _ _ _ hz]; exact hB z hz
    · rw [ht_def, Set.piecewise_eq_of_notMem _ _ _ hz]
      simpa using (norm_nonneg _).trans (hB 0 (by simp; positivity))
  -- step 1: rotation invariance
  have hstep1 : ∀ θ : ℝ, ∫ y, ht (x - cexp (θ * I) * y) * ζ y = ∫ y, ht (x - y) * ζ y := by
    intro θ
    have := integral_comp_rotation (fun y => ht (x - y) * ζ y) θ
    simpa [hrad] using this
  -- step 2: Fubini
  set F : ℝ → ℂ → ℝ := fun θ y => ht (x - cexp (θ * I) * y) * ζ y with hF
  have hFint : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℂ => (fun _ : ℝ => B) p.1 * ‖ζ p.2‖)
        ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) :=
      (integrable_const B).mul_prod hζ.norm
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous fun p : ℝ × ℂ => x - cexp (p.1 * I) * p.2 := by fun_prop
      exact (htm.comp hc.measurable).aestronglyMeasurable.mul hζ.aestronglyMeasurable.comp_snd
    · simp only [Function.uncurry, hF, norm_mul]
      exact mul_le_mul_of_nonneg_right (hbt _) (norm_nonneg _)
  have hswap := integral_integral_swap hFint
  have hL : ∫ θ in Ioc 0 (2 * Real.pi), ∫ y, F θ y = 2 * Real.pi * ∫ y, ht (x - y) * ζ y := by
    simp only [hF, hstep1]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), sub_zero, smul_eq_mul]
  have hR : ∫ y, ∫ θ in Ioc 0 (2 * Real.pi), F θ y = 0 := by
    have : ∀ y, ∫ θ in Ioc 0 (2 * Real.pi), F θ y = (2 * Real.pi * h x) * ζ y := by
      intro y
      simp only [hF, heq]
      rw [integral_mul_const]
      by_cases hy : ‖y‖ ≤ a
      · rw [circle_mean_rotated hh (by linarith)]
      · rw [hsupp y (not_le.mp hy)]; simp
    simp only [this]
    rw [integral_const_mul, hmass, mul_zero]
  have hfin : ∫ y, ht (x - y) * ζ y = 0 := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have := hL.symm.trans (hswap.trans hR)
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hpi.ne'
    · exact h0
  have := heq 0
  simp only [ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at this
  rw [← hfin]
  exact integral_congr_ae (Eventually.of_forall fun y => (this y).symm)

/-- **Corollary `cs:cor:periodic`, radial reference.** For a radial (rotation-invariant),
integrable, zero-mass `ζ` supported in `B̄_a`, the periodic correction velocity vanishes:
the gradient of `x ↦ ∫ (c|x - y|² + h(x - y)) ζ(y) dy` is zero for `|x| < a`. -/
theorem radial_reference_zero_correction {h ζ : ℂ → ℝ} {a : ℝ} (c : ℝ) (ha : 0 < a)
    (hh : InnerProductSpace.HarmonicOnNhd h (ball 0 (8 * a))) (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (hrad : ∀ (θ : ℝ) (y : ℂ), ζ (cexp (θ * I) * y) = ζ y)
    (hmass : ∫ y, ζ y = 0) {x : ℂ} (hx : ‖x‖ < a) :
    fderiv ℝ (fun x => ∫ y, (c * ‖x - y‖ ^ 2 + h (x - y)) * ζ y) x = 0 := by
  have hsym : ∀ y, ζ (I * y) = ζ y := by
    intro y
    have := hrad (Real.pi / 2) y
    rwa [show ((Real.pi / 2 : ℝ) : ℂ) * I = (Real.pi / 2 : ℂ) * I by push_cast; ring,
      Complex.exp_pi_div_two_mul_I] at this
  have hsub3 : closedBall (0 : ℂ) (3 * a) ⊆ ball 0 (8 * a) := closedBall_subset_ball (by linarith)
  have hhc : ContinuousOn h (closedBall 0 (3 * a)) :=
    (fun z hz => (hh z (hsub3 hz)).1.continuousAt.continuousWithinAt)
  obtain ⟨Bh, hBh⟩ := (isCompact_closedBall (0 : ℂ) (3 * a)).exists_bound_of_continuousOn hhc
  have hx' : x ∈ ball (0 : ℂ) a := mem_ball_zero_iff.mpr hx
  have hev : (fun x => ∫ y, (c * ‖x - y‖ ^ 2 + h (x - y)) * ζ y) =ᶠ[nhds x]
      (fun _ => c * ∫ y, ‖y‖ ^ 2 * ζ y) := by
    filter_upwards [isOpen_ball.mem_nhds hx'] with x' hx''
    have hx'n : ‖x'‖ < a := mem_ball_zero_iff.mp hx''
    have hq : Integrable (fun y => c * (‖x' - y‖ ^ 2 * ζ y)) := by
      have h1 : Integrable (fun y => ‖x' - y‖ ^ 2 * ζ y) := by
        have := integrable_rconv (h := fun z => ‖z‖ ^ 2) (r := 3 * a) (B := (3 * a) ^ 2) (x := x')
          hζ hsupp (by fun_prop) (fun z hz => by
            show ‖‖z‖ ^ 2‖ ≤ (3 * a) ^ 2
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hz) 2)
          (by linarith)
        simpa using this
      exact h1.const_mul c
    have hhint := integrable_rconv hζ hsupp hhc hBh (x := x') (by linarith)
    simp only [add_mul, mul_assoc]
    rw [integral_add hq hhint, integral_const_mul, integral_sq_norm_sub_mul hζ hsupp hmass hsym,
      radial_harmonic_conv_zero ha hh hζ hsupp hrad hmass hx'n.le, add_zero]
  rw [hev.fderiv_eq, fderiv_const_apply]

end Euler2D
