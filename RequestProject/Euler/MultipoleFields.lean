module

public import Mathlib
public import RequestProject.Euler.Exterior

/-!
# Planar velocity estimates of Section `part:cs`

Using the complex Biot–Savart velocity `velocityC` of `Euler/Exterior.lean`, we prove the
planar parts of three lemmas of the paper.

* **Lemma `cs:lem:velocity`** (*Velocity from mass and amplitude*):
  `‖K * ω‖_∞ ≤ 2 ‖ω‖₁^{1/2} ‖ω‖_∞^{1/2}` (`velocity_mass_amplitude`).
* **Lemma `cs:lem:outer-field`** (*Interior field of an outer perturbation*): a
  fourfold-symmetric perturbation `η` vanishing in `B_R` satisfies
  `|K * η(z)| ≤ (8/(15π)) |z|³ R⁻⁴ ‖η‖₁` for `|z| ≤ R/2` (`outer_perturbation_field`).
* **Lemma `cs:lem:exterior-remainder`** (*Exterior multipole remainder*): for a
  fourfold-symmetric zero-mass `ζ` supported in `B̄_S` and `2S ≤ |z|`, the velocity differs
  from its fourth-moment field `(i/2π) N₄ \bar z^{-5}` by at most
  `(8/(15π)) |z|^{-9} ∫ |w|⁸ |ζ(w)| dw` (`exterior_multipole_remainder`).
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate Set

namespace Euler2D

/-- Truncated `|v|⁻¹` kernel. -/
noncomputable def truncInvNorm (d : ℝ) (v : ℂ) : ℝ := if ‖v‖ < d then ‖v‖⁻¹ else 0

/-- Radial profile of the truncated kernel. -/
lemma truncInvNorm_aux (d : ℝ) :
    EqOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • (if y < d then y⁻¹ else 0))
      (indicator (Iio d) (fun _ => (1 : ℝ))) (Ioi 0) := by
  intro y hy
  simp only [Complex.finrank_real_complex, smul_eq_mul, indicator, mem_Iio]
  split_ifs <;> simp_all [ne_of_gt (mem_Ioi.mp hy)]

/-- The truncated kernel is integrable. -/
lemma integrable_truncInvNorm (d : ℝ) : Integrable (truncInvNorm d) := by
  have := (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun y : ℝ => if y < d then y⁻¹ else 0)).mpr ?_
  · exact this
  rw [IntegrableOn, integrable_congr ((ae_restrict_mem measurableSet_Ioi).mono
    fun y hy => truncInvNorm_aux d hy)]
  refine (integrable_indicator_iff measurableSet_Iio).mpr ?_
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact integrableOn_const (by simp) (by simp)

/-- `∫_{B_d} |v|⁻¹ dv = 2πd`. -/
lemma integral_truncInvNorm {d : ℝ} (hd : 0 < d) : ∫ v, truncInvNorm d v = 2 * Real.pi * d := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun y : ℝ => if y < d then y⁻¹ else 0)
  have h2 : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [h2, setIntegral_congr_fun measurableSet_Ioi (truncInvNorm_aux d),
    integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio] at h
  simp only [Complex.finrank_real_complex, integral_const, smul_eq_mul, mul_one] at h
  rw [show (truncInvNorm d) = fun v => if ‖v‖ < d then ‖v‖⁻¹ else 0 from rfl, h]
  simp [Measure.real, Iio_inter_Ioi, hd.le]
  ring

/-- The modulus of the Biot–Savart integrand. -/
lemma norm_velocity_integrand (ω : ℂ → ℝ) (z w : ℂ) :
    ‖(ω w : ℂ) * (I * (z - w) / (2 * Real.pi * ‖z - w‖ ^ 2))‖ =
      |ω w| / (2 * Real.pi * ‖z - w‖) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rcases eq_or_ne (z - w) 0 with h | h
  · simp [h]
  have hn : 0 < ‖z - w‖ := norm_pos_iff.mpr h
  have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]; norm_num
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_mul, Complex.norm_I,
    norm_mul, norm_pow, h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  field_simp

/-- Splitting the Biot–Savart integral at distance `d`: `|K * ω(z)| ≤ M d + ‖ω‖₁/(2πd)`. -/
lemma velocity_bound_split {ω : ℂ → ℝ} {M : ℝ} (hω : Integrable ω)
    (hM : ∀ w, |ω w| ≤ M) (z : ℂ) {d : ℝ} (hd : 0 < d) :
    ‖velocityC ω z‖ ≤ M * d + (∫ w, |ω w|) / (2 * Real.pi * d) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set g : ℂ → ℝ := fun w => (M * truncInvNorm d (z - w) + |ω w| / d) / (2 * Real.pi) with hg
  have hgint : Integrable g :=
    (((integrable_truncInvNorm d).comp_sub_left z).const_mul M |>.add
      (hω.abs.div_const d)).div_const _
  have hbd : ∀ w, ‖(ω w : ℂ) * (I * (z - w) / (2 * Real.pi * ‖z - w‖ ^ 2))‖ ≤ g w := by
    intro w
    rw [norm_velocity_integrand, hg]
    simp only [truncInvNorm]
    rw [div_mul_eq_div_div_swap]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hdw : 0 ≤ ‖z - w‖ := norm_nonneg _
    split_ifs with hlt
    · rcases eq_or_lt_of_le hdw with h0 | hpos
      · rw [← h0]; simp; positivity
      calc |ω w| / ‖z - w‖ ≤ M * ‖z - w‖⁻¹ := by
            rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (hM w) (by positivity)
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · rw [mul_zero, zero_add]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hd (not_lt.mp hlt)
  calc ‖velocityC ω z‖ ≤ ∫ w, g w :=
        norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hbd)
    _ = M * d + (∫ w, |ω w|) / (2 * Real.pi * d) := by
        rw [hg, integral_div, integral_add (((integrable_truncInvNorm d).comp_sub_left z).const_mul M)
          (hω.abs.div_const d), integral_const_mul, integral_div,
          integral_sub_left_eq_self (fun v => truncInvNorm d v), integral_truncInvNorm hd]
        field_simp

/-- **Lemma `cs:lem:velocity`** (planar part). If `ω` is integrable and `|ω| ≤ M` everywhere,
then `|K * ω(z)| ≤ 2 (∫|ω|)^{1/2} M^{1/2}` at every point `z`. -/
theorem velocity_mass_amplitude {ω : ℂ → ℝ} {M : ℝ} (hω : Integrable ω)
    (hM : ∀ w, |ω w| ≤ M) (z : ℂ) :
    ‖velocityC ω z‖ ≤ 2 * Real.sqrt (∫ w, |ω w|) * Real.sqrt M := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi1 : 1 < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set A := ∫ w, |ω w| with hA
  have hA0 : 0 ≤ A := integral_nonneg fun w => abs_nonneg _
  have key := fun d (hd : 0 < d) => velocity_bound_split hω hM z hd
  rw [← hA] at key
  rcases eq_or_lt_of_le hA0 with hA' | hApos
  · rw [← hA']
    simp only [Real.sqrt_zero, mul_zero, zero_mul]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (ε / (M + 1)) (by positivity)
    rw [← hA', zero_div, add_zero] at this
    refine this.trans ?_
    rw [zero_add, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  rcases eq_or_lt_of_le hM0 with hM' | hMpos
  · rw [← hM']
    simp only [Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key ((A + 1) / (2 * Real.pi * ε)) (by positivity)
    rw [← hM', zero_mul, zero_add] at this
    refine this.trans ?_
    rw [zero_add, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hsA := Real.sqrt_pos.mpr hApos
  have hsM := Real.sqrt_pos.mpr hMpos
  have := key (Real.sqrt A / Real.sqrt M) (by positivity)
  refine this.trans ?_
  have eA : A = Real.sqrt A ^ 2 := (Real.sq_sqrt hA0).symm
  have eM : M = Real.sqrt M ^ 2 := (Real.sq_sqrt hM0).symm
  have h1 : M * (Real.sqrt A / Real.sqrt M) = Real.sqrt A * Real.sqrt M := by
    rw [eM]; field_simp; rw [Real.sqrt_sq hsM.le]
  have h2 : A / (2 * Real.pi * (Real.sqrt A / Real.sqrt M)) =
      Real.sqrt A * Real.sqrt M / (2 * Real.pi) := by
    rw [eA]; field_simp; rw [Real.sqrt_sq hsA.le]
  rw [h1, h2]
  have : Real.sqrt A * Real.sqrt M / (2 * Real.pi) ≤ Real.sqrt A * Real.sqrt M :=
    div_le_self (by positivity) hpi1.le
  linarith

/-- Rotation by a quarter turn preserves Lebesgue measure. -/
lemma integral_comp_I_mul (f : ℂ → ℂ) : ∫ w, f (I * w) = ∫ w, f w := by
  have hI : ((Circle.exp (Real.pi / 2) : Circle) : ℂ) = I := by
    rw [Circle.coe_exp]; push_cast
    rw [show (Real.pi : ℂ) / 2 * I = (Real.pi / 2 : ℂ) * I by ring, Complex.exp_pi_div_two_mul_I]
  have h := (rotation (Circle.exp (Real.pi / 2))).measurePreserving.integral_comp
    (rotation (Circle.exp (Real.pi / 2))).toHomeomorph.measurableEmbedding f
  simpa [rotation_apply, hI] using h

/-- The root-of-unity identity `¼ Σ_q (z - i^q w)⁻¹ = z³/(z⁴ - w⁴)`. -/
lemma fourfold_cauchy_sum {z w : ℂ} (h : ‖z‖ < ‖w‖) :
    ∑ q ∈ Finset.range 4, (z - I ^ q * w)⁻¹ = 4 * (z ^ 3 / (z ^ 4 - w ^ 4)) := by
  have hne : ∀ u : ℂ, ‖u‖ = ‖w‖ → z - u ≠ 0 := by
    intro u hu h0; rw [sub_eq_zero] at h0; rw [h0, hu] at h; exact lt_irrefl _ h
  have h1 : z - w ≠ 0 := hne w rfl
  have h2 : z - I * w ≠ 0 := hne _ (by simp)
  have h3 : z + w ≠ 0 := by
    have := hne (-w) (by simp); rwa [sub_neg_eq_add] at this
  have h4 : z + I * w ≠ 0 := by
    have := hne (-(I * w)) (by simp); rwa [sub_neg_eq_add] at this
  have hfac : z ^ 4 - w ^ 4 = (z - w) * (z - I * w) * (z + w) * (z + I * w) := by
    ring_nf; rw [Complex.I_sq]; ring_nf
  have h5 : z ^ 4 - w ^ 4 ≠ 0 := by rw [hfac]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_mul, pow_one, zero_add]
  have e2 : z - I ^ 2 * w = z + w := by rw [Complex.I_sq]; ring
  have e3 : z - I ^ 3 * w = z + I * w := by
    rw [pow_succ, Complex.I_sq]; ring
  rw [e2, e3, hfac]
  have h2' : z - w * I ≠ 0 := by rwa [mul_comm]
  have h4' : z + w * I ≠ 0 := by rwa [mul_comm]
  field_simp
  ring_nf; rw [Complex.I_sq]; ring_nf

/-- **Lemma `cs:lem:outer-field`** (planar part). If `η` is integrable, fourfold symmetric and
vanishes in the open disk `B_R`, `R > 0`, then for `|z| ≤ R/2`
`|K * η(z)| ≤ (8/(15π)) |z|³ R⁻⁴ ∫|η|`. -/
theorem outer_perturbation_field {η : ℂ → ℝ} {R : ℝ} (hR : 0 < R) (hη : Integrable η)
    (hsym : ∀ w, η (I * w) = η w) (hzero : ∀ w, ‖w‖ < R → η w = 0) {z : ℂ}
    (hz : ‖z‖ ≤ R / 2) :
    ‖velocityC η z‖ ≤ 8 / (15 * Real.pi) * ‖z‖ ^ 3 / R ^ 4 * ∫ w, |η w| := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set F : ℕ → ℂ → ℂ := fun q w => (η w : ℂ) * (z - I ^ q * w)⁻¹ with hF
  have hFint : ∀ q, Integrable (F q) := by
    intro q
    refine Integrable.mono' (hη.norm.mul_const (2 / R)) ?_ (Filter.Eventually.of_forall ?_)
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hη.1).mul
        ((measurable_const.sub (measurable_const.mul measurable_id)).inv.aestronglyMeasurable)
    · intro w
      by_cases hw : η w = 0
      · simp [hF, hw]
      have hwR : R ≤ ‖w‖ := not_lt.mp fun h => hw (hzero w h)
      have hd : R / 2 ≤ ‖z - I ^ q * w‖ := by
        have := norm_sub_norm_le (I ^ q * w) z
        rw [norm_sub_rev] at this
        simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul] at this
        linarith
      simp only [hF, norm_mul, norm_inv, Complex.norm_real]
      gcongr
      rw [inv_le_comm₀ (by linarith) (by positivity)]
      rw [inv_div]; exact hd
  have hrotq : ∀ q, ∫ w, F q w = ∫ w, F 0 w := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [← ih, ← integral_comp_I_mul (F q)]
      congr 1; funext w
      simp only [hF, hsym, pow_succ]; ring_nf
  have hsum : ∫ w, (η w : ℂ) * (4 * (z ^ 3 / (z ^ 4 - w ^ 4))) = 4 * ∫ w, F 0 w := by
    have : ∫ w, ∑ q ∈ Finset.range 4, F q w = ∑ q ∈ Finset.range 4, ∫ w, F q w :=
      integral_finset_sum _ fun q _ => hFint q
    simp only [hrotq, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    push_cast at this
    rw [← this]
    congr 1; funext w
    by_cases hw : η w = 0
    · simp [hF, hw]
    have hwR : R ≤ ‖w‖ := not_lt.mp fun h => hw (hzero w h)
    rw [← fourfold_cauchy_sum (by linarith), Finset.mul_sum]
  have hu : ‖velocityC η z‖ = 1 / (2 * Real.pi) * ‖∫ w, (η w : ℂ) * (z ^ 3 / (z ^ 4 - w ^ 4))‖ := by
    rw [← Complex.norm_conj, conj_velocityC]
    have h0 : ∫ w, F 0 w = ∫ w, (η w : ℂ) * (z - w)⁻¹ := by simp [hF]
    have h4 : ∫ w, (η w : ℂ) * (z ^ 3 / (z ^ 4 - w ^ 4)) = ∫ w, (η w : ℂ) * (z - w)⁻¹ := by
      rw [← h0]
      have := hsum
      simp_rw [mul_left_comm _ (4 : ℂ)] at this
      rw [integral_const_mul] at this
      exact mul_left_cancel₀ (by norm_num) this
    rw [h4, norm_mul, norm_neg, norm_div, Complex.norm_I, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpi, Complex.norm_ofNat]
  rw [hu]
  have hb : ∀ w, ‖(η w : ℂ) * (z ^ 3 / (z ^ 4 - w ^ 4))‖ ≤ |η w| * (16 / 15 * ‖z‖ ^ 3 / R ^ 4) := by
    intro w
    by_cases hw : η w = 0
    · simp [hw]
    have hwR : R ≤ ‖w‖ := not_lt.mp fun h => hw (hzero w h)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hz4 : ‖z‖ ^ 4 ≤ ‖w‖ ^ 4 / 16 := by
      have : ‖z‖ ≤ ‖w‖ / 2 := by linarith
      calc ‖z‖ ^ 4 ≤ (‖w‖ / 2) ^ 4 := by gcongr
        _ = ‖w‖ ^ 4 / 16 := by ring
    have hlow : 15 / 16 * R ^ 4 ≤ ‖z ^ 4 - w ^ 4‖ := by
      have := norm_sub_norm_le (w ^ 4) (z ^ 4)
      rw [norm_sub_rev (w ^ 4), norm_pow, norm_pow] at this
      have : R ^ 4 ≤ ‖w‖ ^ 4 := by gcongr
      linarith
    rw [div_le_div_iff₀ (by linarith [pow_pos hR 4]) (by positivity)]
    nlinarith [pow_nonneg (norm_nonneg z) 3]
  calc 1 / (2 * Real.pi) * ‖∫ w, (η w : ℂ) * (z ^ 3 / (z ^ 4 - w ^ 4))‖
      ≤ 1 / (2 * Real.pi) * ∫ w, |η w| * (16 / 15 * ‖z‖ ^ 3 / R ^ 4) := by
        gcongr
        exact norm_integral_le_of_norm_le (hη.abs.mul_const _) (Filter.Eventually.of_forall hb)
    _ = _ := by
        rw [integral_mul_const]; field_simp; ring

/-- Multipole expansion of the velocity outside the support. -/
lemma velocityC_hasSum {ζ : ℂ → ℝ} {S : ℝ} (hζ : Integrable ζ)
    (hsupp : ∀ w, S < ‖w‖ → ζ w = 0) {z : ℂ} (hz : S < ‖z‖) :
    HasSum (fun m : ℕ => I / (2 * Real.pi) * momentN ζ m * (conj z ^ (m + 1))⁻¹)
      (velocityC ζ z) := by
  have h1 := (hasSum_cauchy_moments hζ hsupp hz).mul_left (-(I / (2 * Real.pi)))
  have h3 := Complex.hasSum_conj'.mpr h1
  rw [← conj_velocityC, Complex.conj_conj] at h3
  convert h3 using 2 with m
  simp only [map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
    map_inv₀, map_pow, conj_momentM]
  ring

/-- `|N_{4j+8}| ≤ S^{4j} ∫ |w|⁸ |ζ|` for `ζ` supported in `B̄_S`. -/
lemma norm_momentN_le {ζ : ℂ → ℝ} {S : ℝ} (hζ : Integrable ζ)
    (hsupp : ∀ w, S < ‖w‖ → ζ w = 0) (j : ℕ) :
    ‖momentN ζ (4 * j + 8)‖ ≤ S ^ (4 * j) * ∫ w, ‖w‖ ^ 8 * |ζ w| := by
  have hint : Integrable (fun w => ‖w‖ ^ 8 * |ζ w|) := by
    refine Integrable.mono' (hζ.abs.const_mul (S ^ 8)) ?_ (Filter.Eventually.of_forall ?_)
    · exact (continuous_norm.pow 8).aestronglyMeasurable.mul hζ.abs.1
    · intro w
      by_cases hw : ζ w = 0
      · simp [hw]
      have hwS : ‖w‖ ≤ S := not_lt.mp fun h => hw (hsupp w h)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
  rw [momentN, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul _) (Filter.Eventually.of_forall fun w => ?_)
  by_cases hw : ζ w = 0
  · simp [hw]
  have hwS : ‖w‖ ≤ S := not_lt.mp fun h => hw (hsupp w h)
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, pow_add]
  have : ‖w‖ ^ (4 * j) ≤ S ^ (4 * j) := by gcongr
  have h8 : 0 ≤ ‖w‖ ^ 8 := by positivity
  nlinarith [abs_nonneg (ζ w), mul_le_mul_of_nonneg_left this (mul_nonneg h8 (abs_nonneg (ζ w)))]

/-- Zero mass and fourfold symmetry kill all moments `N_m` with `m` not a positive multiple
of `4`. -/
lemma momentN_eq_zero_of_not_mem {ζ : ℂ → ℝ} (hmass : ∫ w, ζ w = 0)
    (hsym : ∀ w, ζ (I * w) = ζ w) {m : ℕ} (hm : m ∉ Set.range (fun j : ℕ => 4 * (j + 1))) :
    momentN ζ m = 0 := by
  rw [← conj_momentM]
  by_cases h4 : 4 ∣ m
  · have hm0 : m = 0 := by
      by_contra hne
      obtain ⟨k, rfl⟩ := h4
      exact hm ⟨k - 1, by simp only; omega⟩
    subst hm0
    simp only [momentM, pow_zero, mul_one]
    rw [integral_complex_ofReal, hmass]; simp
  · rw [momentM_eq_zero_of_not_dvd hsym h4, map_zero]

/-- **Lemma `cs:lem:exterior-remainder`** (planar part). If `ζ` is integrable, fourfold
symmetric, has zero mass and vanishes outside `B̄_S`, and `z ≠ 0` with `2S ≤ |z|`, then the
velocity differs from the fourth-moment field `(i/2π) N₄ \bar z^{-5}` by at most
`(8/(15π)) |z|^{-9} ∫ |w|⁸ |ζ(w)| dw`. -/
theorem exterior_multipole_remainder {ζ : ℂ → ℝ} {S : ℝ} (hζ : Integrable ζ)
    (hsupp : ∀ w, S < ‖w‖ → ζ w = 0) (hmass : ∫ w, ζ w = 0) (hsym : ∀ w, ζ (I * w) = ζ w)
    {z : ℂ} (hz0 : z ≠ 0) (hz : 2 * S ≤ ‖z‖) :
    ‖velocityC ζ z - I / (2 * Real.pi) * momentN ζ 4 * (conj z ^ 5)⁻¹‖ ≤
      8 / (15 * Real.pi) * (∫ w, ‖w‖ ^ 8 * |ζ w|) / ‖z‖ ^ 9 := by
  set S' := max S 0 with hS'
  have hS'0 : 0 ≤ S' := le_max_right _ _
  have hsupp' : ∀ w, S' < ‖w‖ → ζ w = 0 := fun w hw => hsupp w ((le_max_left _ _).trans_lt hw)
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hz' : 2 * S' ≤ ‖z‖ := by
    rcases le_total S 0 with h | h
    · rw [hS', max_eq_right h]; linarith
    · rw [hS', max_eq_left h]; exact hz
  have hzS : S' < ‖z‖ := by linarith
  set A := ∫ w, ‖w‖ ^ 8 * |ζ w| with hA
  have hA0 : 0 ≤ A := integral_nonneg fun w => by positivity
  set g : ℕ → ℂ := fun m => I / (2 * Real.pi) * momentN ζ m * (conj z ^ (m + 1))⁻¹ with hg
  have h1 : HasSum g (velocityC ζ z) := velocityC_hasSum hζ hsupp' hzS
  have hinj : Function.Injective (fun j : ℕ => 4 * (j + 1)) := fun a b h => by
    simp only at h; omega
  have hvan : ∀ m ∉ Set.range (fun j : ℕ => 4 * (j + 1)), g m = 0 := by
    intro m hm
    simp [hg, momentN_eq_zero_of_not_mem hmass hsym hm]
  have h2 : HasSum (fun j => g (4 * (j + 1))) (velocityC ζ z) := (hinj.hasSum_iff hvan).mpr h1
  have h3 := (hasSum_nat_add_iff' 1).mpr h2
  simp only [Finset.range_one, Finset.sum_singleton] at h3
  have hg0 : g (4 * (0 + 1)) = I / (2 * Real.pi) * momentN ζ 4 * (conj z ^ 5)⁻¹ := by
    simp [hg]
  rw [hg0] at h3
  set c : ℝ := 1 / (2 * Real.pi) * A / ‖z‖ ^ 9 with hc
  have hgeo : HasSum (fun j : ℕ => c * (1 / 16 : ℝ) ^ j) (c * (1 - 1 / 16)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c
  have hbound : ∀ j : ℕ, ‖g (4 * (j + 1 + 1))‖ ≤ c * (1 / 16 : ℝ) ^ j := by
    intro j
    have hm : 4 * (j + 1 + 1) = 4 * j + 8 := by ring
    have hpi : 0 < Real.pi := Real.pi_pos
    simp only [hg, hm, norm_mul, norm_div, Complex.norm_I, Complex.norm_real, norm_inv,
      norm_pow, Complex.norm_conj, Real.norm_eq_abs, abs_of_pos hpi, Complex.norm_ofNat]
    have hN := norm_momentN_le hζ hsupp' j
    have hq : S' ^ (4 * j) / ‖z‖ ^ (4 * j) ≤ (1 / 16 : ℝ) ^ j := by
      rw [← div_pow, pow_mul]
      gcongr
      rw [div_pow, div_le_iff₀ (by positivity)]
      nlinarith [pow_le_pow_left₀ hS'0 (show S' ≤ ‖z‖ / 2 by linarith) 4]
    rw [hc]
    have e : ‖z‖ ^ (4 * j + 8 + 1) = ‖z‖ ^ (4 * j) * ‖z‖ ^ 9 := by ring
    rw [e]
    have hz9 : 0 < ‖z‖ ^ 9 := by positivity
    have hz4 : 0 < ‖z‖ ^ (4 * j) := by positivity
    calc 1 / (2 * Real.pi) * ‖momentN ζ (4 * j + 8)‖ * (‖z‖ ^ (4 * j) * ‖z‖ ^ 9)⁻¹
        ≤ 1 / (2 * Real.pi) * (S' ^ (4 * j) * A) * (‖z‖ ^ (4 * j) * ‖z‖ ^ 9)⁻¹ := by gcongr
      _ = 1 / (2 * Real.pi) * A / ‖z‖ ^ 9 * (S' ^ (4 * j) / ‖z‖ ^ (4 * j)) := by
          field_simp
      _ ≤ 1 / (2 * Real.pi) * A / ‖z‖ ^ 9 * (1 / 16) ^ j := mul_le_mul_of_nonneg_left hq (div_nonneg (mul_nonneg (by positivity) hA0) hz9.le)
  have := h3.norm_le_of_bounded hgeo hbound
  calc _ ≤ c * (1 - 1 / 16)⁻¹ := this
    _ = _ := by rw [hc]; field_simp; ring

end Euler2D

end
