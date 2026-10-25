module

public import RequestProject.Euler.RadialSobolev
public import RequestProject.Euler.VelocityDatumSeries

/-!
# Localized Sobolev estimates for scaled physical velocity blocks

The first derivative bound scales with the vorticity amplitude `A`,
while its support has radius `r`. Together these give the paper's
`A * r^(2/q)` Sobolev majorant.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

noncomputable section

namespace Euler2D

lemma deriv_profileAverage_cellOmegaSq_eq_zero {ε s : ℝ} (hε : 0 < ε) (hs : 1 ≤ s) :
    deriv (profileAverage cellOmegaSq ε) s = 0 := by
  rw [deriv_profileAverage continuous_cellOmegaSq,
    cellOmegaSq_eq_zero_of_one_le _ (by linarith), cellOmegaSq_eq_zero_of_one_le _ hs]
  simp

lemma radialAverage_eq_zero_of_one_le_norm {ε : ℝ} (hε : 0 < ε) (c x : R2)
    (hx : 1 ≤ ‖x - c‖) : radialVelocity (profileAverage cellOmegaSq ε) c x = 0 := by
  have hs : 1 ≤ ‖x - c‖ ^ 2 := by nlinarith
  rw [radialVelocity, profileAverage_eq_zero continuous_cellOmegaSq
    cellOmegaSq_eq_zero_of_one_le hε hs, zero_smul]

lemma pd_radialAverage_eq_zero_of_one_le_norm {ε : ℝ} (hε : 0 < ε)
    (c x : R2) (i : Fin 2) (hx : 1 ≤ ‖x - c‖) :
    pd i (radialVelocity (profileAverage cellOmegaSq ε) c) x = 0 := by
  have hs : 1 ≤ ‖x - c‖ ^ 2 := by nlinarith
  unfold pd
  rw [fderiv_radialVelocity_apply
    ((contDiff_profileAverage continuous_cellOmegaSq ε).differentiable one_ne_zero)]
  rw [deriv_profileAverage_cellOmegaSq_eq_zero hε hs,
    profileAverage_eq_zero continuous_cellOmegaSq cellOmegaSq_eq_zero_of_one_le hε hs]
  simp

lemma norm_radialAverage_global_le_half {ε : ℝ} (hε : 0 < ε) (c x : R2) :
    ‖radialVelocity (profileAverage cellOmegaSq ε) c x‖ ≤ 1 / 2 := by
  by_cases hx : ‖x - c‖ ≤ 1
  · unfold radialVelocity
    rw [norm_smul, norm_perpJ]
    exact (mul_le_mul (norm_profileAverage_cellOmegaSq_le_half hε (sq_nonneg _))
      hx (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · rw [radialAverage_eq_zero_of_one_le_norm hε c x (lt_of_not_ge hx).le, norm_zero]
    norm_num

lemma norm_pd_radialVelocity_le_of_bounds {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (c x : R2) (i : Fin 2) {L C D : ℝ}
    (hL : 0 ≤ L) (_hC : 0 ≤ C) (hD : 0 ≤ D)
    (hd : ‖deriv f (‖x - c‖ ^ 2)‖ ≤ L) (hv : ‖f (‖x - c‖ ^ 2)‖ ≤ C)
    (hz : ‖x - c‖ ≤ D) : ‖pd i (radialVelocity f c) x‖ ≤ 2 * L * D ^ 2 + C := by
  have hi : |inner ℝ (x - c) (EuclideanSpace.single i 1)| ≤ D := by
    calc
      |inner ℝ (x - c) (EuclideanSpace.single i 1)| ≤
          ‖x - c‖ * ‖EuclideanSpace.single i 1‖ := abs_real_inner_le_norm _ _
      _ = ‖x - c‖ := by simp
      _ ≤ D := hz
  unfold pd
  rw [fderiv_radialVelocity_apply hf]
  calc
    ‖(2 * deriv f (‖x - c‖ ^ 2) * inner ℝ (x - c) (EuclideanSpace.single i 1)) •
        perpJ (x - c) + f (‖x - c‖ ^ 2) • perpJ (EuclideanSpace.single i 1)‖ ≤
      ‖(2 * deriv f (‖x - c‖ ^ 2) * inner ℝ (x - c) (EuclideanSpace.single i 1)) •
        perpJ (x - c)‖ + ‖f (‖x - c‖ ^ 2) • perpJ (EuclideanSpace.single i 1)‖ :=
      norm_add_le _ _
    _ = (2 * ‖deriv f (‖x - c‖ ^ 2)‖ *
        |inner ℝ (x - c) (EuclideanSpace.single i 1)|) * ‖x - c‖ + ‖f (‖x - c‖ ^ 2)‖ := by
      rw [norm_smul, norm_smul, norm_perpJ, norm_perpJ]
      simp [norm_mul, Real.norm_eq_abs]
    _ ≤ (2 * L * D) * D + C := by gcongr
    _ = 2 * L * D ^ 2 + C := by ring

/-- A scale-independent global derivative bound, using the actual unit
support rather than a bound on the entire coordinate square. -/
lemma norm_pd_radialAverage_global_le_seven {ε : ℝ} (hε : 0 < ε)
    (c x : R2) (i : Fin 2) :
    ‖pd i (radialVelocity (profileAverage cellOmegaSq ε) c) x‖ ≤ 7 := by
  by_cases hx : ‖x - c‖ ≤ 1
  · have h := norm_pd_radialVelocity_le_of_bounds
      ((contDiff_profileAverage continuous_cellOmegaSq ε).differentiable one_ne_zero) c x i
      (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 1 / 2) zero_le_one
      (norm_deriv_profileAverage_cellOmegaSq_le_three hε _)
      (norm_profileAverage_cellOmegaSq_le_half hε (sq_nonneg _)) hx
    norm_num at h
    linarith
  · rw [pd_radialAverage_eq_zero_of_one_le_norm hε c x i (lt_of_not_ge hx).le, norm_zero]
    norm_num

/-- A genuine scaled smooth velocity block in the coordinate disk. -/
def scaledRadialAverage (A r ε : ℝ) (x : R2) : R2 :=
  (A * r) • radialVelocity (profileAverage cellOmegaSq ε) 0 (r⁻¹ • (x - torusCenter))

lemma contDiff_scaledRadialAverage (A r ε : ℝ) : ContDiff ℝ 1 (scaledRadialAverage A r ε) := by
  have hs : ContDiff ℝ 1 (fun x : R2 => r⁻¹ • (x - torusCenter)) :=
    (contDiff_const_smul r⁻¹).comp
      ((contDiff_id : ContDiff ℝ 1 (fun x : R2 => x)).sub contDiff_const)
  exact ContDiff.const_smul (A * r)
    ((contDiff_radialVelocity (contDiff_profileAverage continuous_cellOmegaSq ε) 0).comp hs)

/-- Classical first derivatives of a physical scaled block carry the
amplitude `A`, with the spatial scale canceled by the chain rule. -/
lemma pd_scaledRadialAverage {r : ℝ} (hr : 0 < r) (A ε : ℝ) (x : R2) (i : Fin 2) :
    pd i (scaledRadialAverage A r ε) x = A •
      pd i (radialVelocity (profileAverage cellOmegaSq ε) 0)
        (r⁻¹ • (x - torusCenter)) := by
  have hz : HasFDerivAt (fun y : R2 => r⁻¹ • (y - torusCenter))
      (r⁻¹ • ContinuousLinearMap.id ℝ R2) x :=
    ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const torusCenter).const_smul r⁻¹
  have hb := ((contDiff_radialVelocity
    (contDiff_profileAverage continuous_cellOmegaSq ε) 0).differentiable one_ne_zero
      (r⁻¹ • (x - torusCenter))).hasFDerivAt
  have hd := (hb.comp x hz).const_smul (A * r)
  have hdf := hd.fderiv
  change fderiv ℝ (scaledRadialAverage A r ε) x = _ at hdf
  unfold pd
  rw [hdf]
  simp [smul_smul, hr.ne']

lemma scaledRadialAverage_eq_zero_of_radius_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (A : ℝ) {x : R2} (hx : r ≤ ‖x - torusCenter‖) : scaledRadialAverage A r ε x = 0 := by
  have hn : 1 ≤ ‖r⁻¹ • (x - torusCenter) - (0 : R2)‖ := by
    rw [sub_zero, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    exact (inv_mul_cancel₀ hr.ne' ▸ mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hr.le))
  rw [scaledRadialAverage, radialAverage_eq_zero_of_one_le_norm hε _ _ hn, smul_zero]

lemma pd_scaledRadialAverage_eq_zero_of_radius_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (A : ℝ) {x : R2} (hx : r ≤ ‖x - torusCenter‖) (i : Fin 2) :
    pd i (scaledRadialAverage A r ε) x = 0 := by
  have hn : 1 ≤ ‖r⁻¹ • (x - torusCenter) - (0 : R2)‖ := by
    rw [sub_zero, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    exact (inv_mul_cancel₀ hr.ne' ▸ mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hr.le))
  rw [pd_scaledRadialAverage hr, pd_radialAverage_eq_zero_of_one_le_norm hε _ _ i hn, smul_zero]

lemma norm_scaledRadialAverage_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) (A : ℝ) (x : R2) :
    ‖scaledRadialAverage A r ε x‖ ≤ |A| * r / 2 := by
  rw [scaledRadialAverage, norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hr]
  have h := norm_radialAverage_global_le_half hε 0 (r⁻¹ • (x - torusCenter))
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg A) hr)]

lemma norm_pd_scaledRadialAverage_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (A : ℝ) (x : R2) (i : Fin 2) : ‖pd i (scaledRadialAverage A r ε) x‖ ≤ 7 * |A| := by
  rw [pd_scaledRadialAverage hr, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (norm_pd_radialAverage_global_le_seven hε _ _ _) (abs_nonneg A)).trans_eq (mul_comm _ _)

lemma scaledRadialAverage_matchesTorusFaces {r ε : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hε : 0 < ε) (A : ℝ) : MatchesTorusFaces (scaledRadialAverage A r ε) := by
  intro x i hx
  have hy : (x + EuclideanSpace.single i (2 * Real.pi)) i = 2 * Real.pi := by
    simp [hx, EuclideanSpace.single_apply]
  have hn (y : R2) (hy : y i = 0 ∨ y i = 2 * Real.pi) : r ≤ ‖y - torusCenter‖ := by
    have hs := one_le_norm_sq_sub_center_of_face y i hy
    have hp := norm_nonneg (y - torusCenter)
    have : 1 ≤ ‖y - torusCenter‖ := by nlinarith
    exact hr1.trans this
  rw [scaledRadialAverage_eq_zero_of_radius_le hr hε A (hn _ (Or.inr hy)),
    scaledRadialAverage_eq_zero_of_radius_le hr hε A (hn _ (Or.inl hx))]

lemma norm_scaledRadialAverage_le_indicator {r ε : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hε : 0 < ε) (A : ℝ) (x : R2) :
    ‖scaledRadialAverage A r ε x‖ ≤ (closedBall torusCenter r).indicator (fun _ => 7 * |A|) x := by
  by_cases hx : x ∈ closedBall torusCenter r
  · rw [Set.indicator_of_mem hx]
    have h := norm_scaledRadialAverage_le hε hr.le A x
    nlinarith [abs_nonneg A]
  · rw [Set.indicator_of_notMem hx,
      scaledRadialAverage_eq_zero_of_radius_le hr hε A (by
        exact (lt_of_not_ge (by simpa [mem_closedBall, dist_eq_norm] using hx)).le), norm_zero]

lemma abs_pd_scaledRadialAverage_le_indicator {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (A : ℝ) (x : R2) (i j : Fin 2) :
    |pd i (scaledRadialAverage A r ε) x j| ≤
      (closedBall torusCenter r).indicator (fun _ => 7 * |A|) x := by
  by_cases hx : x ∈ closedBall torusCenter r
  · rw [Set.indicator_of_mem hx]
    exact (abs_coord_le _ j).trans (norm_pd_scaledRadialAverage_le hε hr A x i)
  · rw [Set.indicator_of_notMem hx,
      pd_scaledRadialAverage_eq_zero_of_radius_le hr hε A (by
        exact (lt_of_not_ge (by simpa [mem_closedBall, dist_eq_norm] using hx)).le) i]
    simp

/-- The actual localized radius enters the Sobolev norm bound before
any summation over blocks. -/
theorem w1pBoundedBy_scaledRadialAverage {r ε : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hε : 0 < ε) (A : ℝ) (q : ENNReal) :
    W1pBoundedBy q (torusLocalizedSobolevBound q (7 * |A|) (closedBall torusCenter r))
      (scaledRadialAverage A r ε) := by
  apply w1pBoundedBy_of_C1_localized_bounds (contDiff_scaledRadialAverage A r ε)
    (scaledRadialAverage_matchesTorusFaces hr hr1 hε A) q (by positivity)
    (closedBall torusCenter r)
  · exact fun x _ => norm_scaledRadialAverage_le_indicator hr hr1 hε A x
  · exact fun i j x _ => abs_pd_scaledRadialAverage_le_indicator hr hε A x i j

lemma norm_cellVelocity_le_half (x : R2) : ‖cellVelocity x‖ ≤ 1 / 2 := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [cellVelocity_eq_sq, norm_smul, norm_perpJ]
    exact (mul_le_mul (norm_cellOmegaSq_le_half _) hx (norm_nonneg _)
      (by norm_num)).trans_eq (by norm_num)
  · rw [cellVelocity_eq_zero_of_one_le_norm (lt_of_not_ge hx).le, norm_zero]
    norm_num

lemma tendsto_scaledRadialAverage (A r : ℝ) (x : R2) :
    Tendsto (fun n => scaledRadialAverage A r (radialApproxScale n) x) atTop
      (𝓝 ((A * r) • cellVelocity (r⁻¹ • (x - torusCenter)))) := by
  have h := ((tendsto_profileAverage continuous_cellOmegaSq
    (‖r⁻¹ • (x - torusCenter)‖ ^ 2)).smul_const
      (perpJ (r⁻¹ • (x - torusCenter)))).const_smul (A * r)
  simpa only [scaledRadialAverage, radialVelocity, sub_zero, cellVelocity_eq_sq] using h

def scaledRadialAverageLp (A r : ℝ) (n : ℕ) : L2T :=
  (continuous_vector_memLp_torus
    (contDiff_scaledRadialAverage A r (radialApproxScale n)).continuous 2).toLp
      (scaledRadialAverage A r (radialApproxScale n))

lemma scaledRadialAverageLp_ae (A r : ℝ) (n : ℕ) :
    (scaledRadialAverageLp A r n : R2 → R2) =ᵐ[μT]
      scaledRadialAverage A r (radialApproxScale n) :=
  (continuous_vector_memLp_torus
    (contDiff_scaledRadialAverage A r (radialApproxScale n)).continuous 2).coeFn_toLp

lemma tendsto_scaledRadialAverageLp {r : ℝ} (hr : 0 < r) (A : ℝ) {v : L2T}
    (hveq : (v : R2 → R2) =ᵐ[μT]
      (fun x => (A * r) • cellVelocity (r⁻¹ • (x - torusCenter)))) :
    Tendsto (scaledRadialAverageLp A r) atTop (𝓝 v) := by
  let V : R2 → R2 := fun x => (A * r) • cellVelocity (r⁻¹ • (x - torusCenter))
  have hV : Continuous V :=
    (continuous_cellVelocity.comp (by fun_prop)).const_smul (A * r)
  have hVbound (x : R2) : ‖V x‖ ≤ |A| * r / 2 := by
    change ‖(A * r) • cellVelocity _‖ ≤ _
    rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hr.le]
    have h := mul_le_mul_of_nonneg_left (norm_cellVelocity_le_half
      (r⁻¹ • (x - torusCenter))) (mul_nonneg (abs_nonneg A) hr.le)
    nlinarith
  let F : ℕ → R2 → ℝ := fun n x =>
    ‖scaledRadialAverage A r (radialApproxScale n) x - V x‖ ^ 2
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μT :=
    ((((contDiff_scaledRadialAverage A r (radialApproxScale n)).continuous.sub hV).norm).pow 2).aestronglyMeasurable
  have hbound (n : ℕ) (x : R2) : ‖F n x‖ ≤ (|A| * r) ^ 2 := by
    have hn : ‖scaledRadialAverage A r (radialApproxScale n) x - V x‖ ≤ |A| * r :=
      (norm_sub_le _ _).trans (by
        have h := norm_scaledRadialAverage_le (radialApproxScale_pos n) hr.le A x
        linarith [hVbound x])
    change ‖‖_‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg A) hr.le)).mpr hn
  have hpoint (x : R2) : Tendsto (fun n => F n x) atTop (𝓝 0) := by
    simpa only [F, V, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (((tendsto_scaledRadialAverage A r x).sub_const (V x)).norm).pow 2
  have hint := tendsto_integral_of_dominated_convergence (μ := μT)
    (F := F) (f := fun _ => (0 : ℝ)) (fun _ => (|A| * r) ^ 2)
    hmeas (integrable_const _) (fun n => Eventually.of_forall (hbound n))
    (Eventually.of_forall hpoint)
  have hsq (n : ℕ) : ‖scaledRadialAverageLp A r n - v‖ ^ 2 = ∫ x, F n x ∂μT := by
    rw [← l2_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (scaledRadialAverageLp A r n) v,
      scaledRadialAverageLp_ae A r n, hveq] with x hsub ha hv
    rw [hsub, Pi.sub_apply, ha, hv]
  have hn2 : Tendsto (fun n => ‖scaledRadialAverageLp A r n - v‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq, integral_zero] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn2.sqrt

/-- The nonsmooth physical block retains the radius-dependent Sobolev
bound of its genuine smooth approximations. -/
theorem w1pBoundedBy_scaledCellVelocity {q : ENNReal} (hq : 2 ≤ q)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (A : ℝ) {v : L2T}
    (hveq : (v : R2 → R2) =ᵐ[μT]
      (fun x => (A * r) • cellVelocity (r⁻¹ • (x - torusCenter)))) :
    W1pBoundedBy q (torusLocalizedSobolevBound q (7 * |A|) (closedBall torusCenter r)) v := by
  apply w1pBoundedBy_of_tendsto hq (tendsto_scaledRadialAverageLp hr A hveq)
  intro n
  exact (w1pBoundedBy_scaledRadialAverage hr hr1 (radialApproxScale_pos n) A q).congr_ae
    (scaledRadialAverageLp_ae A r n).symm

theorem w1pBoundedBy_velocityDatumTermLp {q : ENNReal} (hq : 2 ≤ q)
    {A₀ b R ρ : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    W1pBoundedBy q
      (torusLocalizedSobolevBound q (7 * |ampScale A₀ b j|)
        (closedBall torusCenter (radScale R ρ j)))
      (velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j) :=
  w1pBoundedBy_scaledCellVelocity hq (radScale_pos hR hρ j)
    (radScale_le_one hR hR1 hρ hρ1 j) (ampScale A₀ b j)
    (coeFn_velocityDatumTermLp hR hρ 2 j)

end Euler2D

end
