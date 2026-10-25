module

public import Mathlib
public import RequestProject.Euler.MultipoleFields

/-!
# Cancellation in the periodic remainder (Lemma `cs:toruslemma`)

The plane is identified with `ℂ`. Near the origin the periodic Green function is
`G_𝕋(z) = (2π)⁻¹ log|z| - |z|²/(16π²) + h(z)` with `h` harmonic and invariant under the
quarter turn. Lemma `cs:toruslemma` says that for a fourfold-symmetric, zero-mass density `ζ`
supported near `0`, the velocity of `(G_𝕋 - G_{ℝ²}) * ζ` is `O(|x|³ ∫ |y|⁴ |ζ|)`.

Since the periodic Green function itself is not constructed in this project, we prove the
lemma for an arbitrary kernel `c |z|² + h(z)` with `h` harmonic on `B_{8a}` and invariant under
`z ↦ iz`, for `|x| ≤ a` and `ζ` supported in `B̄_a` (`periodic_remainder_cancellation`).
The constant depends only on `h` and `a`.

The proof is the paper's: the quadratic part contributes a constant, and for the harmonic part
we use the holomorphic function `g = ∂ₓh - i ∂ᵧh`, the vanishing of the moments
`∫ yᵏ ζ`, `k ≤ 3`, and the rotational covariance `g(iz) = -i g(z)`, together with Taylor
remainders for holomorphic functions.
-/

@[expose] public section

open MeasureTheory Complex Metric Set Filter

namespace Euler2D

/-- Taylor remainder for a holomorphic function, from Cauchy's estimate: if `f` is holomorphic
on `B̄(c, ρ)` and bounded by `B` on the circle, then at `|z - c| ≤ ρ/2` the error of the degree
`< m` Taylor polynomial is at most `2B (|z - c|/ρ)ᵐ`. -/
lemma taylor_tail_bound {f : ℂ → ℂ} {c z : ℂ} {ρ B : ℝ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (closedBall c ρ)) (hB : ∀ w ∈ sphere c ρ, ‖f w‖ ≤ B)
    (hz : ‖z - c‖ ≤ ρ / 2) (m : ℕ) :
    ‖f z - ∑ n ∈ Finset.range m, (n.factorial : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c‖
      ≤ 2 * B * (‖z - c‖ / ρ) ^ m := by
  have hzb : z ∈ ball c ρ := by rw [mem_ball, dist_eq_norm]; linarith
  have hs := Complex.hasSum_taylorSeries_on_ball (hf.mono ball_subset_closedBall) hzb
  set q := ‖z - c‖ / ρ with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq : q ≤ 1 / 2 := by rw [hqdef, div_le_iff₀ hρ]; linarith
  have hdc : DiffContOnCl ℂ f (ball c ρ) := by
    apply DifferentiableOn.diffContOnCl; rwa [closure_ball _ hρ.ne']
  have hterm : ∀ n, ‖(n.factorial : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c‖ ≤ B * q ^ n := by
    intro n
    have hC := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ hdc hB
    rw [norm_smul, norm_smul, norm_inv, norm_natCast, norm_pow]
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc (n.factorial : ℝ)⁻¹ * (‖z - c‖ ^ n * ‖iteratedDeriv n f c‖)
        ≤ (n.factorial : ℝ)⁻¹ * (‖z - c‖ ^ n * (n.factorial * B / ρ ^ n)) := by gcongr
      _ = B * q ^ n := by rw [hqdef, div_pow]; field_simp
  have htail := (hasSum_nat_add_iff' m).mpr hs
  have hgeom : HasSum (fun n => B * q ^ (n + m)) (B * q ^ m * (1 - q)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left (B * q ^ m)
    convert this using 1; funext n; ring
  have hle := htail.norm_le_of_bounded hgeom (fun n => hterm (n + m))
  have hB0 : 0 ≤ B := by
    have hmem : c + (ρ : ℂ) ∈ sphere c ρ := by
      simp [abs_of_pos hρ]
    exact le_trans (norm_nonneg _) (hB _ hmem)
  have h1q : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc _ ≤ B * q ^ m * (1 - q)⁻¹ := hle
    _ ≤ B * q ^ m * 2 := by gcongr
    _ = 2 * B * q ^ m := by ring

/-- The complex derivative `∂ₓh - i ∂ᵧh` of a real function on the plane. -/
noncomputable def cpartial (h : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ h z 1 : ℂ) - I * (fderiv ℝ h z I : ℂ)

lemma fderiv_eq_re_cpartial {h : ℂ → ℝ} {w : ℂ} (v : ℂ) :
    fderiv ℝ h w v = (cpartial h w * v).re := by
  have hv : v = v.re • (1 : ℂ) + v.im • I := by apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]
  simp [cpartial, smul_eq_mul]
  ring

lemma norm_fderiv_le_cpartial (h : ℂ → ℝ) (w : ℂ) : ‖fderiv ℝ h w‖ ≤ ‖cpartial h w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [fderiv_eq_re_cpartial, Real.norm_eq_abs, ← norm_mul]
  exact abs_re_le_norm _

lemma cpartial_rot {h : ℂ → ℝ} {ρ : ℝ} (hrot : ∀ z ∈ ball (0 : ℂ) ρ, h (I * z) = h z)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) : cpartial h (I * w) = -I * cpartial h w := by
  have hI : ((Circle.exp (Real.pi / 2) : Circle) : ℂ) = I := by
    rw [Circle.coe_exp]; push_cast
    rw [show (Real.pi : ℂ) / 2 * I = (Real.pi / 2 : ℂ) * I by ring, Complex.exp_pi_div_two_mul_I]
  set R : ℂ ≃L[ℝ] ℂ := (rotation (Circle.exp (Real.pi / 2))).toContinuousLinearEquiv with hR
  have hRapp : ∀ z, R z = I * z := by
    intro z; simp [hR, rotation_apply, hI]
  have hloc : (h ∘ R) =ᶠ[nhds w] h := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    simp [hRapp, hrot z hz]
  have key := R.comp_right_fderiv (f := h) (x := w)
  rw [hloc.fderiv_eq, hRapp] at key
  have hv : ∀ v, fderiv ℝ h (I * w) (I * v) = fderiv ℝ h w v := by
    intro v
    have := congrArg (fun L => L v) key
    simpa [hRapp] using this.symm
  have e1 : fderiv ℝ h (I * w) 1 = - fderiv ℝ h w I := by
    have := hv (-I)
    rw [show I * -I = (1 : ℂ) by rw [mul_neg, I_mul_I, neg_neg]] at this
    rw [this, map_neg]
  have e2 : fderiv ℝ h (I * w) I = fderiv ℝ h w 1 := by
    have := hv 1
    rwa [mul_one] at this
  simp only [cpartial, e1, e2]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- Products of a function supported in a measurable set `K` with a function continuous on
`K` are a.e.-strongly measurable. -/
lemma aestronglyMeasurable_mul_of_supp {u v : ℂ → ℂ} {K : Set ℂ} (hK : MeasurableSet K)
    (hu : AEStronglyMeasurable u) (hsupp : ∀ y, y ∉ K → u y = 0) (hv : ContinuousOn v K) :
    AEStronglyMeasurable (fun y => u y * v y) := by
  have heq : (fun y => u y * v y) = K.indicator (fun y => u y * v y) := by
    funext y; by_cases hy : y ∈ K <;> simp [hy, hsupp]
  rw [heq, aestronglyMeasurable_indicator_iff hK]
  exact hu.restrict.mul (hv.aestronglyMeasurable hK)

/-- Real-scalar version of `aestronglyMeasurable_mul_of_supp`. -/
lemma aestronglyMeasurable_smul_of_supp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℂ → ℝ} {v : ℂ → E} {K : Set ℂ} (hK : MeasurableSet K)
    (hu : AEStronglyMeasurable u) (hsupp : ∀ y, y ∉ K → u y = 0) (hv : ContinuousOn v K) :
    AEStronglyMeasurable (fun y => u y • v y) := by
  have heq : (fun y => u y • v y) = K.indicator (fun y => u y • v y) := by
    funext y; by_cases hy : y ∈ K <;> simp [hy, hsupp]
  rw [heq, aestronglyMeasurable_indicator_iff hK]
  exact hu.restrict.smul (hv.aestronglyMeasurable hK)

/-- Convolution of a real density with a complex kernel, `∫ ζ(y) g(w - y) dy`. -/
noncomputable def cconv (ζ : ℂ → ℝ) (g : ℂ → ℂ) (w : ℂ) : ℂ := ∫ y, (ζ y : ℂ) * g (w - y)

/-- Zero mass and fourfold symmetry kill the holomorphic moments of order `< 4`. -/
lemma momentM_eq_zero_of_lt_four {ζ : ℂ → ℝ} (hmass : ∫ y, ζ y = 0)
    (hsym : ∀ y, ζ (I * y) = ζ y) {k : ℕ} (hk : k < 4) : momentM ζ k = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [momentM, pow_zero, mul_one]; rw [integral_complex_ofReal, hmass]; simp
  · exact momentM_eq_zero_of_not_dvd hsym (fun h4 => by obtain ⟨j, rfl⟩ := h4; omega)

lemma integrable_mul_pow_of_supp {ζ : ℂ → ℝ} {a : ℝ} (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (k : ℕ) :
    Integrable (fun y => (ζ y : ℂ) * y ^ k) := by
  refine Integrable.mono' (hζ.norm.const_mul (max a 0 ^ k))
    (((Complex.continuous_ofReal.comp_aestronglyMeasurable hζ.aestronglyMeasurable)).mul (continuous_pow k).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  by_cases hy : ζ y = 0
  · simp [hy]
  have hya : ‖y‖ ≤ max a 0 := le_max_of_le_left (not_lt.mp fun h => hy (hsupp y h))
  rw [norm_mul, norm_real, norm_pow, mul_comm]
  gcongr

lemma integrable_norm_pow_mul_of_supp {ζ : ℂ → ℝ} {a : ℝ} (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (k : ℕ) :
    Integrable (fun y => ‖y‖ ^ k * |ζ y|) := by
  refine Integrable.mono' (hζ.norm.const_mul (max a 0 ^ k))
    ((continuous_norm.pow k).aestronglyMeasurable.mul hζ.aestronglyMeasurable.norm)
    (Eventually.of_forall fun y => ?_)
  by_cases hy : ζ y = 0
  · simp [hy]
  have hya : ‖y‖ ≤ max a 0 := le_max_of_le_left (not_lt.mp fun h => hy (hsupp y h))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_abs, Real.norm_eq_abs]
  gcongr

/-- Integrability of `ζ(y) g(w - y)` when `g` is continuous and bounded on the relevant disk. -/
lemma integrable_cconv {ζ : ℂ → ℝ} {g : ℂ → ℂ} {a r Bg : ℝ} {w : ℂ} (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (hg : ContinuousOn g (closedBall 0 r))
    (hgB : ∀ z ∈ closedBall (0 : ℂ) r, ‖g z‖ ≤ Bg) (hw : ‖w‖ + a ≤ r) :
    Integrable (fun y => (ζ y : ℂ) * g (w - y)) := by
  have hmeas : AEStronglyMeasurable (fun y => (ζ y : ℂ) * g (w - y)) := by
    apply aestronglyMeasurable_mul_of_supp (K := closedBall 0 a) measurableSet_closedBall
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hζ.aestronglyMeasurable)
    · intro y hy
      simp only [mem_closedBall, dist_zero_right, not_le] at hy
      simp [hsupp y hy]
    · refine hg.comp (continuous_const.sub continuous_id).continuousOn fun y hy => ?_
      simp only [mem_closedBall, dist_zero_right] at hy ⊢
      calc ‖w - y‖ ≤ ‖w‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ r := by linarith
  refine Integrable.mono' (hζ.norm.const_mul Bg) hmeas (Eventually.of_forall fun y => ?_)
  by_cases hy : ζ y = 0
  · simp [hy]
  have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
  have hwy : w - y ∈ closedBall (0 : ℂ) r := by
    simp only [mem_closedBall, dist_zero_right]
    calc ‖w - y‖ ≤ ‖w‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ r := by linarith
  rw [norm_mul, norm_real, mul_comm]
  gcongr
  exact hgB _ hwy

/-- The `y`-step: Taylor expansion of `g(w - ·)` to degree three is annihilated by `ζ`, so
`|∫ ζ(y) g(w - y) dy| ≤ 2 B_g (4a)⁻⁴ ∫ |y|⁴ |ζ|` for `|w| ≤ 2a`. -/
lemma cconv_bound {ζ : ℂ → ℝ} {g : ℂ → ℂ} {a Bg : ℝ} (ha : 0 < a) (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (hmass : ∫ y, ζ y = 0) (hsym : ∀ y, ζ (I * y) = ζ y)
    (hg : DifferentiableOn ℂ g (ball 0 (8 * a)))
    (hgB : ∀ z ∈ closedBall (0 : ℂ) (6 * a), ‖g z‖ ≤ Bg) {w : ℂ} (hw : ‖w‖ ≤ 2 * a) :
    ‖cconv ζ g w‖ ≤ 2 * Bg / (4 * a) ^ 4 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  have h4a : 0 < 4 * a := by linarith
  set T : ℂ → ℂ := fun y => ∑ n ∈ Finset.range 4,
    (n.factorial : ℂ)⁻¹ • ((w - y) - w) ^ n • iteratedDeriv n g w with hT
  have hsub : closedBall w (4 * a) ⊆ closedBall 0 (6 * a) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_closedBall_zero_iff]
    calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 6 * a := by linarith
  have hgd : DifferentiableOn ℂ g (closedBall w (4 * a)) :=
    hg.mono (hsub.trans (closedBall_subset_ball (by linarith)))
  have hsph : ∀ z ∈ sphere w (4 * a), ‖g z‖ ≤ Bg :=
    fun z hz => hgB z (hsub (sphere_subset_closedBall hz))
  have hpt : ∀ y, ‖(ζ y : ℂ) * (g (w - y) - T y)‖ ≤ 2 * Bg / (4 * a) ^ 4 * (‖y‖ ^ 4 * |ζ y|) := by
    intro y
    by_cases hy : ζ y = 0
    · simp [hy]
    have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
    have e : ‖w - y - w‖ = ‖y‖ := by rw [show w - y - w = -y by ring, norm_neg]
    have := taylor_tail_bound h4a hgd hsph (z := w - y) (by rw [e]; linarith) 4
    rw [e] at this
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    calc |ζ y| * ‖g (w - y) - T y‖ ≤ |ζ y| * (2 * Bg * (‖y‖ / (4 * a)) ^ 4) := by gcongr
      _ = _ := by rw [div_pow]; ring
  have hterm : ∀ n : ℕ, (fun y => (ζ y : ℂ) * ((n.factorial : ℂ)⁻¹ • ((w - y) - w) ^ n •
      iteratedDeriv n g w)) = fun y => ((n.factorial : ℂ)⁻¹ * (-1) ^ n * iteratedDeriv n g w) *
      ((ζ y : ℂ) * y ^ n) := by
    intro n; funext y
    rw [show w - y - w = (-1) * y by ring, mul_pow, smul_eq_mul, smul_eq_mul]; ring
  have hint2 : Integrable (fun y => (ζ y : ℂ) * T y) := by
    simp only [hT, Finset.mul_sum]
    refine integrable_finset_sum _ fun n _ => ?_
    rw [hterm n]
    exact (integrable_mul_pow_of_supp hζ hsupp n).const_mul _
  have hTint : ∫ y, (ζ y : ℂ) * T y = 0 := by
    simp only [hT, Finset.mul_sum]
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero fun n hn => ?_
      rw [hterm n, integral_const_mul]
      have := momentM_eq_zero_of_lt_four hmass hsym (Finset.mem_range.mp hn)
      rw [momentM] at this
      rw [this, mul_zero]
    · intro n _
      rw [hterm n]
      exact (integrable_mul_pow_of_supp hζ hsupp n).const_mul _
  have hint1 : Integrable (fun y => (ζ y : ℂ) * g (w - y)) :=
    integrable_cconv hζ hsupp (r := 6 * a)
      (hg.continuousOn.mono (closedBall_subset_ball (by linarith))) hgB (by linarith)
  calc ‖cconv ζ g w‖ = ‖∫ y, (ζ y : ℂ) * (g (w - y) - T y)‖ := by
        rw [cconv]; congr 1; simp_rw [mul_sub]; rw [integral_sub hint1 hint2, hTint, sub_zero]
    _ ≤ ∫ y, 2 * Bg / (4 * a) ^ 4 * (‖y‖ ^ 4 * |ζ y|) :=
        norm_integral_le_of_norm_le ((integrable_norm_pow_mul_of_supp hζ hsupp 4).const_mul _)
          (Eventually.of_forall hpt)
    _ = _ := integral_const_mul _ _

/-- `w ↦ ∫ ζ(y) g(w - y) dy` is holomorphic on `B_{3a}`. -/
lemma cconv_differentiableOn {ζ : ℂ → ℝ} {g : ℂ → ℂ} {a : ℝ} (ha : 0 < a) (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (hg : DifferentiableOn ℂ g (ball 0 (8 * a))) :
    DifferentiableOn ℂ (cconv ζ g) (ball 0 (3 * a)) := by
  have hsub4 : closedBall (0 : ℂ) (4 * a) ⊆ ball 0 (8 * a) := closedBall_subset_ball (by linarith)
  have hgc : ContinuousOn g (closedBall 0 (4 * a)) := hg.continuousOn.mono hsub4
  have hg'c : ContinuousOn (deriv g) (closedBall 0 (4 * a)) :=
    (hg.deriv isOpen_ball).continuousOn.mono hsub4
  obtain ⟨Bg, hBg⟩ := (isCompact_closedBall (0 : ℂ) (4 * a)).exists_bound_of_continuousOn hgc
  obtain ⟨Bd, hBd⟩ := (isCompact_closedBall (0 : ℂ) (4 * a)).exists_bound_of_continuousOn hg'c
  have hmem : ∀ w ∈ ball (0 : ℂ) (3 * a), ∀ y : ℂ, ‖y‖ ≤ a → w - y ∈ closedBall (0 : ℂ) (4 * a) := by
    intro w hw y hy
    rw [mem_ball_zero_iff] at hw
    rw [mem_closedBall_zero_iff]
    calc ‖w - y‖ ≤ ‖w‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 4 * a := by linarith
  intro w₀ hw₀
  have hw₀' : ‖w₀‖ < 3 * a := mem_ball_zero_iff.mp hw₀
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w y => (ζ y : ℂ) * g (w - y)) (F' := fun w y => (ζ y : ℂ) * deriv g (w - y))
    (x₀ := w₀) (bound := fun y => Bd * ‖ζ y‖) (isOpen_ball.mem_nhds hw₀)
    (by
      filter_upwards [isOpen_ball.mem_nhds hw₀] with w hw
      exact (integrable_cconv hζ hsupp hgc hBg
        (by have := mem_ball_zero_iff.mp hw; linarith)).aestronglyMeasurable)
    (integrable_cconv hζ hsupp hgc hBg (by linarith))
    (integrable_cconv hζ hsupp hg'c hBd (by linarith)).aestronglyMeasurable
    (Eventually.of_forall fun y w hw => by
      by_cases hy : ζ y = 0
      · simp [hy]
      have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
      show ‖(ζ y : ℂ) * deriv g (w - y)‖ ≤ Bd * ‖ζ y‖
      rw [norm_mul, norm_real, mul_comm]
      exact mul_le_mul_of_nonneg_right (hBd _ (hmem w hw y hya)) (norm_nonneg _))
    (hζ.norm.const_mul Bd)
    (Eventually.of_forall fun y w hw => by
      by_cases hy : ζ y = 0
      · simp only [hy, ofReal_zero, zero_mul]; exact hasDerivAt_const w 0
      have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
      have hgw : DifferentiableAt ℂ g (w - y) :=
        hg.differentiableAt (isOpen_ball.mem_nhds (hsub4 (hmem w hw y hya)))
      exact (hgw.hasDerivAt.comp w ((hasDerivAt_id w).sub_const y)).const_mul _ |>.congr_deriv
        (by simp))
  exact key.2.differentiableAt.differentiableWithinAt

/-- Rotational covariance of the convolution. -/
lemma cconv_rot {ζ : ℂ → ℝ} {g : ℂ → ℂ} {a : ℝ} (hsupp : ∀ y, a < ‖y‖ → ζ y = 0)
    (hsym : ∀ y, ζ (I * y) = ζ y) (hgrot : ∀ z ∈ ball (0 : ℂ) (8 * a), g (I * z) = -I * g z)
    {x : ℂ} (hx : ‖x‖ < 7 * a) : cconv ζ g (I * x) = -I * cconv ζ g x := by
  have hcomp := integral_comp_I_mul (fun y => (ζ y : ℂ) * g (I * x - y))
  unfold cconv
  rw [← hcomp, ← integral_const_mul]
  congr 1; funext y
  rw [hsym]
  by_cases hy : ζ y = 0
  · simp [hy]
  have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
  have hxy : x - y ∈ ball (0 : ℂ) (8 * a) := by
    simp only [mem_ball, dist_zero_right]
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ < 8 * a := by linarith
  rw [show I * x - I * y = I * (x - y) by ring, hgrot _ hxy]; ring

/-- A holomorphic function on `B̄_{2a}` with `P(ix) = -i P(x)` and `|P| ≤ B` on the circle
satisfies `|P(x)| ≤ 2B (|x|/2a)³` for `|x| ≤ a`. -/
lemma cubic_vanishing_bound {P : ℂ → ℂ} {a B : ℝ} (ha : 0 < a)
    (hP : DifferentiableOn ℂ P (closedBall 0 (2 * a)))
    (hrot : ∀ x ∈ closedBall (0 : ℂ) (2 * a), P (I * x) = -I * P x)
    (hB : ∀ w ∈ sphere (0 : ℂ) (2 * a), ‖P w‖ ≤ B) {x : ℂ} (hx : ‖x‖ ≤ a) :
    ‖P x‖ ≤ 2 * B * (‖x‖ / (2 * a)) ^ 3 := by
  have h2a : 0 < 2 * a := by linarith
  have hxI : ∀ j : ℕ, ‖I ^ j * x‖ = ‖x‖ := by intro j; simp [norm_pow]
  have hPj : ∀ j : ℕ, P (I ^ j * x) = (-I) ^ j * P x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_assoc, hrot _ (by rw [mem_closedBall_zero_iff, hxI j]; linarith), ih]
      ring
  set T : ℂ → ℂ := fun z => ∑ n ∈ Finset.range 3,
    (n.factorial : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n P 0 with hT
  have hE : ∀ j : ℕ, ‖P (I ^ j * x) - T (I ^ j * x)‖ ≤ 2 * B * (‖x‖ / (2 * a)) ^ 3 := by
    intro j
    have := taylor_tail_bound (c := 0) (z := I ^ j * x) h2a hP hB
      (by rw [sub_zero, hxI j]; linarith) 3
    simpa only [hT, sub_zero, hxI j] using this
  have hsumT : ∑ j ∈ Finset.range 4, I ^ j * T (I ^ j * x) = 0 := by
    simp only [hT, Finset.sum_range_succ, Finset.sum_range_zero, sub_zero, smul_eq_mul]
    ring_nf
    simp only [I_sq, I_pow_four, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring,
      show I ^ 6 = -1 by rw [show 6 = 4 + 2 by rfl, pow_add, I_pow_four, I_sq]; ring,
      show I ^ 9 = I by rw [show 9 = 4 + 4 + 1 by rfl, pow_add, pow_add, I_pow_four]; ring]
    ring
  have h4 : (4 : ℂ) * P x = ∑ j ∈ Finset.range 4, I ^ j * P (I ^ j * x) := by
    simp only [hPj, Finset.sum_range_succ, Finset.sum_range_zero]
    ring_nf
    simp only [I_sq, I_pow_four,
      show I ^ 6 = -1 by rw [show 6 = 4 + 2 by rfl, pow_add, I_pow_four, I_sq]; ring]
    ring
  have h4' : (4 : ℂ) * P x = ∑ j ∈ Finset.range 4, I ^ j * (P (I ^ j * x) - T (I ^ j * x)) := by
    rw [h4]
    simp only [mul_sub, Finset.sum_sub_distrib, hsumT, sub_zero]
  have hnorm : ‖(4 : ℂ) * P x‖ ≤ 4 * (2 * B * (‖x‖ / (2 * a)) ^ 3) := by
    rw [h4']
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ Finset.range 4, ‖I ^ j * (P (I ^ j * x) - T (I ^ j * x))‖
        ≤ ∑ j ∈ Finset.range 4, 2 * B * (‖x‖ / (2 * a)) ^ 3 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow, norm_I, one_pow, one_mul]
          exact hE j
      _ = 4 * (2 * B * (‖x‖ / (2 * a)) ^ 3) := by simp
  rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num] at hnorm
  linarith

/-- Differentiation under the integral: the gradient of `x ↦ ∫ h(x - y) ζ(y) dy` is
controlled by the holomorphic convolution with `∂ₓh - i∂ᵧh`. -/
lemma norm_fderiv_conv_le {h : ℂ → ℝ} {ζ : ℂ → ℝ} {a : ℝ} (ha : 0 < a)
    (hh : InnerProductSpace.HarmonicOnNhd h (ball 0 (8 * a))) (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) {x : ℂ} (hx : ‖x‖ ≤ a) :
    ‖fderiv ℝ (fun x => ∫ y, h (x - y) * ζ y) x‖ ≤ ‖cconv ζ (cpartial h) x‖ := by
  have hsub3 : closedBall (0 : ℂ) (3 * a) ⊆ ball 0 (8 * a) := closedBall_subset_ball (by linarith)
  have hcd : ContDiffOn ℝ 2 h (ball 0 (8 * a)) := fun z hz => (hh z hz).1.contDiffWithinAt
  have hhc : ContinuousOn h (closedBall 0 (3 * a)) := hcd.continuousOn.mono hsub3
  have hfc : ContinuousOn (fderiv ℝ h) (closedBall 0 (3 * a)) :=
    (hcd.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).mono hsub3
  have hgd : DifferentiableOn ℂ (cpartial h) (ball 0 (8 * a)) := fun z hz =>
    (HarmonicAt.differentiableAt_complex_partial (hh z hz)).differentiableWithinAt
  have hgc : ContinuousOn (cpartial h) (closedBall 0 (3 * a)) := hgd.continuousOn.mono hsub3
  obtain ⟨Bh, hBh⟩ := (isCompact_closedBall (0 : ℂ) (3 * a)).exists_bound_of_continuousOn hhc
  obtain ⟨Bd, hBd⟩ := (isCompact_closedBall (0 : ℂ) (3 * a)).exists_bound_of_continuousOn hfc
  obtain ⟨Bg, hBg⟩ := (isCompact_closedBall (0 : ℂ) (3 * a)).exists_bound_of_continuousOn hgc
  have hmem : ∀ x' ∈ ball (0 : ℂ) (2 * a), ∀ y : ℂ, ‖y‖ ≤ a →
      x' - y ∈ closedBall (0 : ℂ) (3 * a) := by
    intro x' hx' y hy
    rw [mem_ball_zero_iff] at hx'
    rw [mem_closedBall_zero_iff]
    calc ‖x' - y‖ ≤ ‖x'‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 3 * a := by linarith
  have hx2 : x ∈ ball (0 : ℂ) (2 * a) := by rw [mem_ball_zero_iff]; linarith
  have hsupp' : ∀ y, y ∉ closedBall (0 : ℂ) a → ζ y = 0 := by
    intro y hy
    simp only [mem_closedBall, dist_zero_right, not_le] at hy
    exact hsupp y hy
  have hFm : ∀ x' ∈ ball (0 : ℂ) (2 * a), AEStronglyMeasurable (fun y => h (x' - y) * ζ y) := by
    intro x' hx'
    have := aestronglyMeasurable_smul_of_supp (K := closedBall 0 a) measurableSet_closedBall
      hζ.aestronglyMeasurable hsupp' (v := fun y => h (x' - y))
      (hhc.comp (continuous_const.sub continuous_id).continuousOn
        (fun y hy => hmem x' hx' y (mem_closedBall_zero_iff.mp hy)))
    simpa [smul_eq_mul, mul_comm] using this
  have hFint : Integrable (fun y => h (x - y) * ζ y) := by
    refine Integrable.mono' (hζ.norm.const_mul Bh) (hFm x hx2) (Eventually.of_forall fun y => ?_)
    by_cases hy : ζ y = 0
    · simp [hy]
    have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hBh _ (hmem x hx2 y hya)) (norm_nonneg _)
  have hF'm : AEStronglyMeasurable (fun y => ζ y • fderiv ℝ h (x - y)) :=
    aestronglyMeasurable_smul_of_supp (K := closedBall 0 a) measurableSet_closedBall
      hζ.aestronglyMeasurable hsupp'
      (hfc.comp (continuous_const.sub continuous_id).continuousOn
        (fun y hy => hmem x hx2 y (mem_closedBall_zero_iff.mp hy)))
  have hF'bd : ∀ y, ∀ x' ∈ ball (0 : ℂ) (2 * a),
      ‖ζ y • fderiv ℝ h (x' - y)‖ ≤ Bd * ‖ζ y‖ := by
    intro y x' hx'
    by_cases hy : ζ y = 0
    · simp [hy]
    have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hBd _ (hmem x' hx' y hya)) (norm_nonneg _)
  have hF'int : Integrable (fun y => ζ y • fderiv ℝ h (x - y)) :=
    Integrable.mono' (hζ.norm.const_mul Bd) hF'm (Eventually.of_forall fun y => hF'bd y x hx2)
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x' y => h (x' - y) * ζ y) (F' := fun x' y => ζ y • fderiv ℝ h (x' - y))
    (x₀ := x) (bound := fun y => Bd * ‖ζ y‖) (isOpen_ball.mem_nhds hx2)
    (by filter_upwards [isOpen_ball.mem_nhds hx2] with x' hx' using hFm x' hx')
    hFint hF'm (Eventually.of_forall fun y x' hx' => hF'bd y x' hx') (hζ.norm.const_mul Bd)
    (Eventually.of_forall fun y x' hx' => by
      by_cases hy : ζ y = 0
      · simp only [hy, mul_zero, zero_smul]; exact hasFDerivAt_const 0 x'
      have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
      have hdiff : DifferentiableAt ℝ h (x' - y) :=
        (hh _ (hsub3 (hmem x' hx' y hya))).1.differentiableAt (by norm_num)
      have := (hdiff.hasFDerivAt.comp x' ((hasFDerivAt_id x').sub_const y)).mul_const (ζ y)
      convert this using 1 <;>
        simp only [Function.comp_apply, id_eq, ContinuousLinearMap.comp_id])
  rw [hderiv.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [ContinuousLinearMap.integral_apply hF'int]
  have hcint : Integrable (fun y => (ζ y : ℂ) * cpartial h (x - y) * v) :=
    (integrable_cconv hζ hsupp hgc hBg (by linarith)).mul_const v
  have hre := integral_re hcint
  simp only [RCLike.re_to_complex] at hre
  have e : ∫ y, (ζ y • fderiv ℝ h (x - y)) v = (cconv ζ (cpartial h) x * v).re := by
    rw [cconv, ← integral_mul_const, ← hre]
    congr 1; funext y
    rw [ContinuousLinearMap.smul_apply, fderiv_eq_re_cpartial, smul_eq_mul, mul_assoc,
      re_ofReal_mul]
  rw [e, Real.norm_eq_abs, ← norm_mul]
  exact abs_re_le_norm _

/-- **Lemma `cs:toruslemma`** for the harmonic part of the kernel. -/
theorem harmonic_remainder_cancellation {h : ℂ → ℝ} {a : ℝ} (ha : 0 < a)
    (hh : InnerProductSpace.HarmonicOnNhd h (ball 0 (8 * a)))
    (hrot : ∀ z ∈ ball (0 : ℂ) (8 * a), h (I * z) = h z) :
    ∃ K : ℝ, ∀ ζ : ℂ → ℝ, Integrable ζ → (∀ y, a < ‖y‖ → ζ y = 0) →
      (∀ y, ζ (I * y) = ζ y) → ∫ y, ζ y = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        ‖fderiv ℝ (fun x => ∫ y, h (x - y) * ζ y) x‖ ≤ K * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  have hgd : DifferentiableOn ℂ (cpartial h) (ball 0 (8 * a)) := fun z hz =>
    (HarmonicAt.differentiableAt_complex_partial (hh z hz)).differentiableWithinAt
  have hcont : ContinuousOn (cpartial h) (closedBall 0 (6 * a)) :=
    hgd.continuousOn.mono (closedBall_subset_ball (by linarith))
  obtain ⟨Bg, hBg⟩ := (isCompact_closedBall (0 : ℂ) (6 * a)).exists_bound_of_continuousOn hcont
  refine ⟨2 * (2 * Bg / (4 * a) ^ 4) / (2 * a) ^ 3, ?_⟩
  intro ζ hζ hsupp hsym hmass x hx
  have hP := cconv_differentiableOn ha hζ hsupp hgd
  have hrotg : ∀ z ∈ ball (0 : ℂ) (8 * a), cpartial h (I * z) = -I * cpartial h z :=
    fun z hz => cpartial_rot hrot hz
  have hPx := cubic_vanishing_bound (P := cconv ζ (cpartial h))
    (B := 2 * Bg / (4 * a) ^ 4 * ∫ y, ‖y‖ ^ 4 * |ζ y|) ha
    (hP.mono (closedBall_subset_ball (by linarith)))
    (fun x hx => cconv_rot hsupp hsym hrotg
      (by have := mem_closedBall_zero_iff.mp hx; linarith))
    (fun w hw => cconv_bound ha hζ hsupp hmass hsym hgd (fun z hz => hBg z hz)
      (by rw [mem_sphere_zero_iff_norm.mp hw])) hx
  calc _ ≤ ‖cconv ζ (cpartial h) x‖ := norm_fderiv_conv_le ha hh hζ hsupp hx
    _ ≤ _ := hPx
    _ = _ := by rw [div_pow]; ring

lemma integrable_norm_pow_mul_of_supp' {ζ : ℂ → ℝ} {a : ℝ} (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (k : ℕ) :
    Integrable (fun y => ‖y‖ ^ k * ζ y) := by
  refine (integrable_norm_pow_mul_of_supp hζ hsupp k).mono'
    ((continuous_norm.pow k).aestronglyMeasurable.mul hζ.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]

/-- The quadratic part of the kernel contributes a constant: for a zero-mass, fourfold-symmetric
`ζ` with bounded support, `∫ |x - y|² ζ(y) dy = ∫ |y|² ζ(y) dy` for every `x`. -/
lemma integral_sq_norm_sub_mul {ζ : ℂ → ℝ} {a : ℝ} (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (hmass : ∫ y, ζ y = 0) (hsym : ∀ y, ζ (I * y) = ζ y)
    (x : ℂ) : ∫ y, ‖x - y‖ ^ 2 * ζ y = ∫ y, ‖y‖ ^ 2 * ζ y := by
  have hM1 := momentM_eq_zero_of_lt_four hmass hsym (k := 1) (by norm_num)
  have hint1 := integrable_mul_pow_of_supp hζ hsupp 1
  simp only [momentM, pow_one] at hM1 hint1
  have hre : ∫ y, y.re * ζ y = 0 := by
    have := integral_re hint1
    simp only [RCLike.re_to_complex, re_ofReal_mul] at this
    rw [hM1, zero_re] at this
    simpa only [mul_comm] using this
  have him : ∫ y, y.im * ζ y = 0 := by
    have := integral_im hint1
    simp only [RCLike.im_to_complex, im_ofReal_mul] at this
    rw [hM1, zero_im] at this
    simpa only [mul_comm] using this
  have hire : Integrable (fun y : ℂ => y.re * ζ y) := by
    have := hint1.re
    simp only [RCLike.re_to_complex, re_ofReal_mul] at this
    simpa only [mul_comm] using this
  have hiim : Integrable (fun y : ℂ => y.im * ζ y) := by
    have := hint1.im
    simp only [RCLike.im_to_complex, im_ofReal_mul] at this
    simpa only [mul_comm] using this
  have hiy2 := integrable_norm_pow_mul_of_supp' hζ hsupp 2
  have hexp : (fun y => ‖x - y‖ ^ 2 * ζ y) = fun y => (‖x‖ ^ 2 * ζ y + ‖y‖ ^ 2 * ζ y) -
      (2 * x.re * (y.re * ζ y) + 2 * x.im * (y.im * ζ y)) := by
    funext y
    simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im]
    ring
  have hA : Integrable (fun y : ℂ => ‖x‖ ^ 2 * ζ y + ‖y‖ ^ 2 * ζ y) :=
    (hζ.const_mul _).add hiy2
  have hB : Integrable (fun y : ℂ => 2 * x.re * (y.re * ζ y) + 2 * x.im * (y.im * ζ y)) :=
    (hire.const_mul _).add (hiim.const_mul _)
  have e1 : ∫ y : ℂ, (‖x‖ ^ 2 * ζ y + ‖y‖ ^ 2 * ζ y) = ∫ y, ‖y‖ ^ 2 * ζ y := by
    rw [integral_add (hζ.const_mul _) hiy2, integral_const_mul, hmass, mul_zero, zero_add]
  have e2 : ∫ y : ℂ, (2 * x.re * (y.re * ζ y) + 2 * x.im * (y.im * ζ y)) = 0 := by
    rw [integral_add (hire.const_mul _) (hiim.const_mul _), integral_const_mul,
      integral_const_mul, hre, him]
    ring
  rw [hexp, integral_sub hA hB, e1, e2, sub_zero]

lemma integrable_rconv {ζ h : ℂ → ℝ} {a r B : ℝ} {x : ℂ} (hζ : Integrable ζ)
    (hsupp : ∀ y, a < ‖y‖ → ζ y = 0) (hh : ContinuousOn h (closedBall 0 r))
    (hB : ∀ z ∈ closedBall (0 : ℂ) r, ‖h z‖ ≤ B) (hx : ‖x‖ + a ≤ r) :
    Integrable (fun y => h (x - y) * ζ y) := by
  have hmem : ∀ y : ℂ, ‖y‖ ≤ a → x - y ∈ closedBall (0 : ℂ) r := by
    intro y hy
    rw [mem_closedBall_zero_iff]
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ r := by linarith
  have hsupp' : ∀ y, y ∉ closedBall (0 : ℂ) a → ζ y = 0 := by
    intro y hy
    simp only [mem_closedBall, dist_zero_right, not_le] at hy
    exact hsupp y hy
  have hm : AEStronglyMeasurable (fun y => h (x - y) * ζ y) := by
    have := aestronglyMeasurable_smul_of_supp (K := closedBall 0 a) measurableSet_closedBall
      hζ.aestronglyMeasurable hsupp' (v := fun y => h (x - y))
      (hh.comp (continuous_const.sub continuous_id).continuousOn
        (fun y hy => hmem y (mem_closedBall_zero_iff.mp hy)))
    simpa [smul_eq_mul, mul_comm] using this
  refine Integrable.mono' (hζ.norm.const_mul B) hm (Eventually.of_forall fun y => ?_)
  by_cases hy : ζ y = 0
  · simp [hy]
  have hya : ‖y‖ ≤ a := not_lt.mp fun h => hy (hsupp y h)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB _ (hmem y hya)) (norm_nonneg _)

/-- **Lemma `cs:toruslemma`** (*Cancellation in the periodic remainder*), planar form. Let the
kernel be `c |z|² + h(z)` with `h` harmonic on `B_{8a}` and invariant under the quarter turn
(for the periodic Green function, `c = -1/(16π²)` and `h` is the smooth harmonic part). There
is a constant `K`, depending only on `h`, `c` and `a`, such that for every integrable,
fourfold-symmetric, zero-mass `ζ` vanishing outside `B̄_a` and every `|x| ≤ a`, the gradient
of the convolution of the kernel with `ζ` satisfies
`|∇[(c|·|² + h) * ζ](x)| ≤ K |x|³ ∫ |y|⁴ |ζ(y)| dy`. -/
theorem periodic_remainder_cancellation {h : ℂ → ℝ} {a : ℝ} (c : ℝ) (ha : 0 < a)
    (hh : InnerProductSpace.HarmonicOnNhd h (ball 0 (8 * a)))
    (hrot : ∀ z ∈ ball (0 : ℂ) (8 * a), h (I * z) = h z) :
    ∃ K : ℝ, ∀ ζ : ℂ → ℝ, Integrable ζ → (∀ y, a < ‖y‖ → ζ y = 0) →
      (∀ y, ζ (I * y) = ζ y) → ∫ y, ζ y = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        ‖fderiv ℝ (fun x => ∫ y, (c * ‖x - y‖ ^ 2 + h (x - y)) * ζ y) x‖
          ≤ K * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  obtain ⟨K, hK⟩ := harmonic_remainder_cancellation ha hh hrot
  refine ⟨K, fun ζ hζ hsupp hsym hmass x hx => ?_⟩
  have hsub3 : closedBall (0 : ℂ) (3 * a) ⊆ ball 0 (8 * a) := closedBall_subset_ball (by linarith)
  have hhc : ContinuousOn h (closedBall 0 (3 * a)) :=
    (fun z hz => (hh z (hsub3 hz)).1.continuousAt.continuousWithinAt)
  obtain ⟨Bh, hBh⟩ := (isCompact_closedBall (0 : ℂ) (3 * a)).exists_bound_of_continuousOn hhc
  have hx2 : x ∈ ball (0 : ℂ) (2 * a) := by rw [mem_ball_zero_iff]; linarith
  have hev : (fun x => ∫ y, (c * ‖x - y‖ ^ 2 + h (x - y)) * ζ y) =ᶠ[nhds x]
      (fun x => (c * ∫ y, ‖y‖ ^ 2 * ζ y) + ∫ y, h (x - y) * ζ y) := by
    filter_upwards [isOpen_ball.mem_nhds hx2] with x' hx'
    have hx'n : ‖x'‖ < 2 * a := mem_ball_zero_iff.mp hx'
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
    rw [integral_add hq hhint, integral_const_mul, integral_sq_norm_sub_mul hζ hsupp hmass hsym]
  rw [hev.fderiv_eq, fderiv_const_add]
  exact hK ζ hζ hsupp hsym hmass x hx

end Euler2D
