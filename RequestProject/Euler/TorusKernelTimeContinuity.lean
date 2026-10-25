module

public import RequestProject.Euler.TorusKernelL2Approximation
public import RequestProject.Euler.TorusKernelVelocityRegularity

/-! Uniform temporal continuity of the actual velocity integral. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ENNReal ContDiff

namespace Euler2D

def scalarL2L1Constant : ℝ := ‖scalarFirstComponent‖ * ‖constE0‖

lemma scalarL2L1Constant_nonneg : 0 ≤ scalarL2L1Constant := mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma integral_norm_scalarL2_le (W : Lp ℝ 2 μT) :
    (∫ x in torusBox, ‖W x‖) ≤ scalarL2L1Constant * ‖W‖ := by
  have hI : Integrable (fun x => ‖W x‖) μT := ((Lp.memLp W).integrable (by norm_num)).norm
  calc
    _ ≤ ∫ x in torusBox, ‖scalarFirstComponent W x‖ * ‖constE0 x‖ := by
      apply integral_mono_ae hI (integrable_norm_mul_norm _ _)
      filter_upwards [scalarFirstComponent_ae W, constE0_ae] with x hx hc
      have h1 : 1 ≤ ‖constE0 x‖ := by simpa only [hc, abs_one] using abs_coord_le (constE0 x) 0
      calc
        ‖W x‖ = |scalarFirstComponent W x 0| := by rw [hx, Real.norm_eq_abs]
        _ ≤ ‖scalarFirstComponent W x‖ := abs_coord_le _ _
        _ ≤ _ := le_mul_of_one_le_right (norm_nonneg _) h1
    _ ≤ ‖scalarFirstComponent W‖ * ‖constE0‖ := l2_integral_mul_norm_le _ _
    _ ≤ (‖scalarFirstComponent‖ * ‖W‖) * ‖constE0‖ :=
      mul_le_mul_of_nonneg_right (scalarFirstComponent.le_opNorm W) (norm_nonneg _)
    _ = _ := by unfold scalarL2L1Constant; ring

lemma integrable_periodic_kernel_sub_left {K : R2 → R2} (hK : Integrable K μT)
    (hp : IsTorusPeriodic K) (x : R2) :
    Integrable (fun y => K (x - y + torusCenter)) μT := by
  have he : (fun y => K (x - y + torusCenter)) = K ∘ (fun y => (x + torusCenter) - y) := by
    funext y
    congr 1
    abel_nf
  rw [he]
  exact (torusAreaPreserving_sub_left _).integrable_comp hK hp

lemma integral_norm_periodic_kernel_sub_left {K : R2 → R2}
    (hK : AEStronglyMeasurable K μT) (hp : IsTorusPeriodic K) (x : R2) :
    (∫ y in torusBox, ‖K (x - y + torusCenter)‖) = ∫ y in torusBox, ‖K y‖ := by
  have hpn : IsTorusPeriodic (fun y => ‖K y‖) := fun y i => congrArg norm (hp y i)
  convert (torusAreaPreserving_sub_left (x + torusCenter)).integral_comp hK.norm hpn using 1
  congr 1
  funext y
  congr 2
  abel

lemma periodic_kernel_bound_sub_left {K : R2 → R2} (hp : IsTorusPeriodic K) {B : ℝ}
    (hB : ∀ᵐ y ∂μT, ‖K y‖ ≤ B) (x : R2) :
    ∀ᵐ y ∂μT, ‖K (x - y + torusCenter)‖ ≤ B := by
  have hm := (torusAreaPreserving_sub_left (x + torusCenter)).quasiMeasurePreserving.ae hB
  filter_upwards [hm] with y hy
  simpa only [Function.comp_apply, hp.eq_torusWrap,
    show x + torusCenter - y = x - y + torusCenter by abel] using hy

def torusApproxKernelVelocity (ε : ℝ) (W : Lp ℝ 2 μT) (x : R2) : R2 :=
  ∫ y in torusBox, W y • torusKernelL2Approx ε (x - y + torusCenter)

def torusKernelApproxBound (ε : ℝ) : ℝ := lpNorm (torusKernelL2Approx ε) ∞ μT

lemma torusKernelApproxBound_nonneg (ε : ℝ) : 0 ≤ torusKernelApproxBound ε := lpNorm_nonneg

lemma torusKernelApproxBound_ae {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ y ∂μT, ‖torusKernelL2Approx ε y‖ ≤ torusKernelApproxBound ε :=
  ae_le_lpNorm_exponent_top (memLp_torusKernelL2Approx hε ∞)

lemma integrable_torusApproxKernelVelocity_integrand {ε : ℝ} (hε : 0 < ε)
    (W : Lp ℝ 2 μT) (x : R2) :
    Integrable (fun y => W y • torusKernelL2Approx ε (x - y + torusCenter)) μT := by
  exact ((Lp.memLp W).integrable (by norm_num)).smul_bdd (torusKernelApproxBound ε)
    (integrable_periodic_kernel_sub_left ((memLp_torusKernelL2Approx hε 1).integrable le_rfl)
      (isTorusPeriodic_torusKernelL2Approx ε) x).aestronglyMeasurable
    (periodic_kernel_bound_sub_left (isTorusPeriodic_torusKernelL2Approx ε) (torusKernelApproxBound_ae hε) x)

theorem norm_torusApproxKernelVelocity_sub_le {ε : ℝ} (hε : 0 < ε)
    (W Z : Lp ℝ 2 μT) (x : R2) :
    ‖torusApproxKernelVelocity ε W x - torusApproxKernelVelocity ε Z x‖ ≤
      (torusKernelApproxBound ε * scalarL2L1Constant) * ‖W - Z‖ := by
  have hb := periodic_kernel_bound_sub_left (isTorusPeriodic_torusKernelL2Approx ε)
    (torusKernelApproxBound_ae hε) x
  have hI : Integrable (fun y => torusKernelApproxBound ε * ‖(W - Z) y‖) μT :=
    (((Lp.memLp (W - Z)).integrable (by norm_num)).norm).const_mul _
  change ‖(∫ y in torusBox, W y • torusKernelL2Approx ε (x - y + torusCenter)) -
    ∫ y in torusBox, Z y • torusKernelL2Approx ε (x - y + torusCenter)‖ ≤ _
  rw [← integral_sub (integrable_torusApproxKernelVelocity_integrand hε W x)
    (integrable_torusApproxKernelVelocity_integrand hε Z x)]
  calc
    _ ≤ ∫ y in torusBox, torusKernelApproxBound ε * ‖(W - Z) y‖ := by
      apply norm_integral_le_of_norm_le hI
      filter_upwards [hb, Lp.coeFn_sub W Z] with y hy he
      rw [← sub_smul, norm_smul, he]
      simpa only [Pi.sub_def, mul_comm] using
        mul_le_mul_of_nonneg_left hy (norm_nonneg (W y - Z y))
    _ = torusKernelApproxBound ε * ∫ y in torusBox, ‖(W - Z) y‖ := integral_const_mul _ _
    _ ≤ torusKernelApproxBound ε * (scalarL2L1Constant * ‖W - Z‖) :=
      mul_le_mul_of_nonneg_left (integral_norm_scalarL2_le _) (torusKernelApproxBound_nonneg ε)
    _ = _ := by ring

theorem norm_torusKernelVelocity_sub_approx_le {ε M : ℝ} (hε : 0 < ε) (hM0 : 0 ≤ M)
    (W : Lp ℝ 2 μT) (hM : ∀ᵐ y ∂μT, ‖W y‖ ≤ M) (x : R2) :
    ‖torusKernelVelocity W x - torusApproxKernelVelocity ε W x‖ ≤ M * ε := by
  let E : R2 → R2 := fun y => torusBiotSavartKernel y - torusKernelL2Approx ε y
  have hEI : Integrable E μT := integrable_torusBiotSavartKernel.sub
    ((memLp_torusKernelL2Approx hε 1).integrable le_rfl)
  have hp : IsTorusPeriodic E := by
    intro y i
    simp only [E, isTorusPeriodic_torusBiotSavartKernel y i, isTorusPeriodic_torusKernelL2Approx ε y i]
  have hI := (integrable_periodic_kernel_sub_left hEI hp x).norm.const_mul M
  change ‖(∫ y in torusBox, W y • torusBiotSavartKernel (x - y + torusCenter)) -
    ∫ y in torusBox, W y • torusKernelL2Approx ε (x - y + torusCenter)‖ ≤ _
  rw [← integral_sub (integrable_torusKernelVelocity_integrand (Lp.aestronglyMeasurable W) hM x)
    (integrable_torusApproxKernelVelocity_integrand hε W x)]
  calc
    _ ≤ ∫ y in torusBox, M * ‖E (x - y + torusCenter)‖ := by
      apply norm_integral_le_of_norm_le hI
      filter_upwards [hM] with y hy
      rw [← smul_sub, norm_smul]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = M * ∫ y in torusBox, ‖E y‖ := by
      rw [integral_const_mul, integral_norm_periodic_kernel_sub_left hEI.1 hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_torusKernelL2Approx_error_le hε.le) hM0

/-- Strong `L²` convergence with a common actual vorticity bound gives
uniform convergence of the integral representatives on the entire plane. -/
theorem tendstoUniformly_torusKernelVelocity_of_tendsto_L2 {ι : Type*} {l : Filter ι}
    {W : ι → Lp ℝ 2 μT} {Z : Lp ℝ 2 μT} (hW : Tendsto W l (𝓝 Z))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ n, ∀ᵐ y ∂μT, ‖W n y‖ ≤ M)
    (hZ : ∀ᵐ y ∂μT, ‖Z y‖ ≤ M) :
    TendstoUniformly (fun n x => torusKernelVelocity (W n) x) (torusKernelVelocity Z) l := by
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  let ε := δ / (8 * (M + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : (M + 1) * ε = δ / 8 := by
    dsimp [ε]
    field_simp
  have hnear : 2 * M * ε ≤ δ / 4 := by nlinarith
  have hdiff : Tendsto (fun n => ‖W n - Z‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hW
  have hlim : Tendsto (fun n => (torusKernelApproxBound ε * scalarL2L1Constant) * ‖W n - Z‖)
      l (𝓝 0) := by simpa only [mul_zero] using hdiff.const_mul (torusKernelApproxBound ε * scalarL2L1Constant)
  have hev : ∀ᶠ n in l,
      (torusKernelApproxBound ε * scalarL2L1Constant) * ‖W n - Z‖ < δ / 2 :=
    hlim.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hev] with n hn x
  have h1 := norm_torusKernelVelocity_sub_approx_le hε hM0 (W n) (hM n) x
  have h2 := norm_torusApproxKernelVelocity_sub_le hε (W n) Z x
  have h3 := norm_torusKernelVelocity_sub_approx_le hε hM0 Z hZ x
  have ht1 := dist_triangle (torusKernelVelocity (W n) x) (torusApproxKernelVelocity ε (W n) x)
    (torusKernelVelocity Z x)
  have ht2 := dist_triangle (torusApproxKernelVelocity ε (W n) x)
    (torusApproxKernelVelocity ε Z x) (torusKernelVelocity Z x)
  simp only [dist_eq_norm] at ht1 ht2
  rw [norm_sub_rev] at h3
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- Joint continuity is obtained from uniform temporal convergence and
the already proved spatial continuity of the actual singular integral. -/
theorem continuous_torusKernelVelocity_of_continuous_L2
    {W : ℝ → Lp ℝ 2 μT} (hW : Continuous W) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ∀ᵐ y ∂μT, ‖W t y‖ ≤ M) :
    Continuous (fun p : ℝ × R2 => torusKernelVelocity (W p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have ht := tendstoUniformly_torusKernelVelocity_of_tendsto_L2 (hW.tendsto p.1) hM0 hM (hM p.1)
  have htime : ∀ᶠ t in 𝓝 p.1, ∀ x,
      dist (torusKernelVelocity (W p.1) x) (torusKernelVelocity (W t) x) < δ / 2 :=
    Metric.tendstoUniformly_iff.mp ht (δ / 2) (by linarith)
  have hs := (continuous_torusKernelVelocity (Lp.aestronglyMeasurable (W p.1)) (hM p.1)).tendsto p.2
  have hspace : ∀ᶠ x in 𝓝 p.2,
      dist (torusKernelVelocity (W p.1) x) (torusKernelVelocity (W p.1) p.2) < δ / 2 :=
    Metric.tendsto_nhds.mp hs (δ / 2) (by linarith)
  filter_upwards [(continuous_fst.tendsto p).eventually htime,
    (continuous_snd.tendsto p).eventually hspace] with q hqt hqx
  have hqt' : dist (torusKernelVelocity (W q.1) q.2) (torusKernelVelocity (W p.1) q.2) < δ / 2 := by
    rw [dist_comm]
    exact hqt q.2
  exact (dist_triangle _ (torusKernelVelocity (W p.1) q.2) _).trans_lt
    ((add_lt_add hqt' hqx).trans_eq (by ring))

lemma torusKernelVelocity_congr_ae {w z : R2 → ℝ} (h : w =ᵐ[μT] z) (x : R2) :
    torusKernelVelocity w x = torusKernelVelocity z x := by
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem continuous_torusKernelVelocity_of_L2_representatives
    {W : ℝ → Lp ℝ 2 μT} {w : ℝ → R2 → ℝ} (hW : Continuous W)
    (hae : ∀ t, (W t : R2 → ℝ) =ᵐ[μT] w t) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ∀ᵐ y ∂μT, ‖w t y‖ ≤ M) :
    Continuous (fun p : ℝ × R2 => torusKernelVelocity (w p.1) p.2) := by
  have hbound (t : ℝ) : ∀ᵐ y ∂μT, ‖W t y‖ ≤ M := by
    filter_upwards [hae t, hM t] with y hy hb
    rw [hy]
    exact hb
  have he : (fun p : ℝ × R2 => torusKernelVelocity (W p.1) p.2) =
      (fun p : ℝ × R2 => torusKernelVelocity (w p.1) p.2) := by
    funext p
    exact torusKernelVelocity_congr_ae (hae p.1) p.2
  rw [← he]
  exact continuous_torusKernelVelocity_of_continuous_L2 hW hM0 hbound

end Euler2D

end
