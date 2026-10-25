module

public import RequestProject.Euler.StreamFunction
public import RequestProject.Euler.ClassicalEuler
public import RequestProject.Euler.FourierRegularization
public import RequestProject.Euler.StationaryLimit
public import RequestProject.Euler.StreamTimeCalculus

/-!
# The vorticity equation implies the original momentum weak equation

The spatial identity is first proved by genuine periodic integration by
parts for smooth fields. Fourier regularization then transfers it to the
actual `L²` velocity and its `L²` distributional curl.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace Euler2D

/-- The perpendicular gradient uses the same orientation as `IsCurl`. -/
def perpGradient (χ : R2 → ℝ) (x : R2) : R2 :=
  torusVec (-pd 1 χ x) (pd 0 χ x)

@[simp] lemma perpGradient_zero (χ : R2 → ℝ) (x : R2) :
    perpGradient χ x 0 = -pd 1 χ x := rfl

@[simp] lemma perpGradient_one (χ : R2 → ℝ) (x : R2) :
    perpGradient χ x 1 = pd 0 χ x := rfl

lemma contDiff_pd_infty {χ : R2 → ℝ} (hχ : ContDiff ℝ ∞ χ) (i : Fin 2) :
    ContDiff ℝ ∞ (pd i χ) :=
  (hχ.fderiv_right (by simp)).clm_apply contDiff_const

lemma contDiff_perpGradient {χ : R2 → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (perpGradient χ) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (contDiff_pd_infty hχ 1).neg
  · exact contDiff_pd_infty hχ 0

lemma isTorusPeriodic_perpGradient {χ : R2 → ℝ} (hχ : IsTorusPeriodic χ) :
    IsTorusPeriodic (perpGradient χ) := by
  intro x i
  ext j
  fin_cases j
  · change -pd 1 χ (x + EuclideanSpace.single i (2 * Real.pi)) = -pd 1 χ x
    rw [isTorusPeriodic_pd hχ 1 x i]
  · change pd 0 χ (x + EuclideanSpace.single i (2 * Real.pi)) = pd 0 χ x
    exact isTorusPeriodic_pd hχ 0 x i

lemma pd_pd_comm {χ : R2 → ℝ} (hχ : ContDiff ℝ ∞ χ) (i j : Fin 2) (x : R2) :
    pd i (pd j χ) x = pd j (pd i χ) x := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ χ) x := hfd.differentiable (by simp) x
  have he (k : Fin 2) :
      pd i (pd k χ) x =
        fderiv ℝ (fderiv ℝ χ) x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) := by
    unfold pd
    rw [(hd.hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single k (1 : ℝ)) x)).fderiv]
    simp
  rw [he]
  have hd' := hd.hasFDerivAt.clm_apply
    (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)
  change HasFDerivAt (pd i χ) _ x at hd'
  rw [pd, hd'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact ((hχ.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq _ _

lemma perpGradient_divergence {χ : R2 → ℝ} (hχ : ContDiff ℝ ∞ χ) (x : R2) :
    pd 0 (perpGradient χ) x 0 + pd 1 (perpGradient χ) x 1 = 0 := by
  have hp := (contDiff_perpGradient hχ).differentiable (by simp) x
  rw [← torus_pd_component _ x hp 0 0, ← torus_pd_component _ x hp 1 1]
  simp only [perpGradient_zero, perpGradient_one]
  rw [show (fun y => -pd 1 χ y) = -(pd 1 χ) from rfl]
  rw [pd, fderiv_neg]
  change -pd 0 (pd 1 χ) x + pd 1 (pd 0 χ) x = 0
  rw [pd_pd_comm hχ]
  ring

def kineticEnergy (u : R2 → R2) (x : R2) : ℝ :=
  (u x 0 * u x 0 + u x 1 * u x 1) / 2

lemma contDiff_kineticEnergy {u : R2 → R2} (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (kineticEnergy u) := by
  have h (i : Fin 2) : ContDiff ℝ 1 (fun x => u x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hu
  exact (((h 0).mul (h 0)).add ((h 1).mul (h 1))).div_const 2

lemma isTorusPeriodic_kineticEnergy {u : R2 → R2} (hu : IsTorusPeriodic u) :
    IsTorusPeriodic (kineticEnergy u) := by
  intro x i
  simp only [kineticEnergy, hu x i]

lemma pd_kineticEnergy {u : R2 → R2} (hu : ContDiff ℝ 1 u) (i : Fin 2) (x : R2) :
    pd i (kineticEnergy u) x = u x 0 * pd i u x 0 + u x 1 * pd i u x 1 := by
  have h (j : Fin 2) := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).hasFDerivAt.comp x
    (hu.differentiable one_ne_zero x).hasFDerivAt
  have he := (((h 0).mul (h 0)).add ((h 1).mul (h 1))).mul_const ((2 : ℝ)⁻¹)
  simp only [← div_eq_mul_inv] at he
  change HasFDerivAt (kineticEnergy u) _ x at he
  rw [pd, he.fderiv]
  simp [pd]
  ring

/-- The smooth spatial vorticity-to-momentum identity, on the actual
fundamental square and without a momentum hypothesis. -/
theorem integral_flux_perpGradient_smooth {u : R2 → R2}
    (hu : ContDiff ℝ 1 u) (hup : IsTorusPeriodic u)
    (hdiv : ∀ x, pd 0 u x 0 + pd 1 u x 1 = 0)
    {χ : R2 → ℝ} (hχ : IsScalarTest χ) :
    (∫ x in torusBox, ∑ i, ∑ j, u x i * u x j * pd j (perpGradient χ) x i) =
      -(∫ x in torusBox, (pd 0 u x 1 - pd 1 u x 0) *
        ∑ i : Fin 2, u x i * pd i χ x) := by
  have hpg : ContDiff ℝ 1 (perpGradient χ) :=
    (contDiff_perpGradient hχ.1).of_le (by simp)
  have hpp := isTorusPeriodic_perpGradient hχ.2
  rw [integral_periodic_flux_by_parts hu hup hpg hpp hdiv]
  have hpoint (x : R2) :
      (∑ i : Fin 2, (∑ j : Fin 2, u x j * pd j u x i) * perpGradient χ x i) =
        (∑ i : Fin 2, pd i (kineticEnergy u) x * perpGradient χ x i) +
          (pd 0 u x 1 - pd 1 u x 0) * ∑ i : Fin 2, u x i * pd i χ x := by
    simp only [Fin.sum_univ_two, perpGradient_zero, perpGradient_one, pd_kineticEnergy hu]
    ring
  simp_rw [hpoint]
  have hI : Integrable (fun x => ∑ i : Fin 2,
      pd i (kineticEnergy u) x * perpGradient χ x i) μT := by
    apply integrable_finset_sum
    intro i _
    exact integrable_torusBox_of_continuous
      ((continuous_pd_of_contDiff_one _ (contDiff_kineticEnergy hu) i).mul
        ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp hpg.continuous))
  have hJ : Integrable (fun x => (pd 0 u x 1 - pd 1 u x 0) *
      ∑ i : Fin 2, u x i * pd i χ x) μT := by
    apply integrable_torusBox_of_continuous
    exact ((((EuclideanSpace.proj 1 : R2 →L[ℝ] ℝ).continuous.comp
      (continuous_pd_of_contDiff_one u hu 0)).sub
      ((EuclideanSpace.proj 0 : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one u hu 1))).mul
      (continuous_finset_sum _ (fun i _ =>
        ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp hu.continuous).mul
          (contDiff_pd_infty hχ.1 i).continuous)))
  rw [integral_add hI hJ, integral_pressure_pairing_eq_zero (contDiff_kineticEnergy hu)
    (isTorusPeriodic_kineticEnergy hup) hpg hpp (perpGradient_divergence hχ.1), zero_add]

/-- A scalar `L²` field as the first component of a vector `L²` field. -/
def scalarFirstComponent : Lp ℝ 2 μT →L[ℝ] L2T :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 0 (1 : ℝ))).compLpL 2 μT

lemma scalarFirstComponent_ae (w : Lp ℝ 2 μT) :
    (fun x => scalarFirstComponent w x 0) =ᵐ[μT] w := by
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : R2)).coeFn_compLpL w] with x hx
  change scalarFirstComponent w x 0 = w x
  change scalarFirstComponent w x = _ at hx
  rw [hx]
  simp [ContinuousLinearMap.toSpanSingleton_apply, EuclideanSpace.single_apply]

lemma integrable_scalar_vector_mul (u : L2T) (w : Lp ℝ 2 μT)
    {k : R2 → ℝ} (hk : Continuous k) (j : Fin 2) :
    Integrable (fun x => w x * u x j * k x) μT := by
  obtain ⟨C, hC⟩ := bound_on_box hk
  apply (integrable_bilin (scalarFirstComponent w) u 0 j hk.aestronglyMeasurable hC).congr
  filter_upwards [scalarFirstComponent_ae w] with x hx
  rw [hx]

lemma tendsto_integral_scalar_vector_mul {ι : Type*} {l : Filter ι}
    {u : ι → L2T} {v : L2T} {w : ι → Lp ℝ 2 μT} {z : Lp ℝ 2 μT}
    (hu : Tendsto u l (𝓝 v)) (hw : Tendsto w l (𝓝 z))
    {k : R2 → ℝ} (hk : Continuous k) (j : Fin 2) :
    Tendsto (fun n => ∫ x in torusBox, w n x * u n x j * k x) l
      (𝓝 (∫ x in torusBox, z x * v x j * k x)) := by
  have he (a : Lp ℝ 2 μT) (b : L2T) :
      (∫ x in torusBox, scalarFirstComponent a x 0 * b x j * k x) =
        ∫ x in torusBox, a x * b x j * k x := by
    apply integral_congr_ae
    filter_upwards [scalarFirstComponent_ae a] with x hx
    rw [hx]
  simpa only [Function.comp_def, he] using tendsto_fixed_bilin
    ((scalarFirstComponent.continuous.tendsto z).comp hw) hu hk 0 j

lemma tendsto_integral_vorticity_transport {ι : Type*} {l : Filter ι}
    {u : ι → L2T} {v : L2T} {w : ι → Lp ℝ 2 μT} {z : Lp ℝ 2 μT}
    (hu : Tendsto u l (𝓝 v)) (hw : Tendsto w l (𝓝 z))
    {χ : R2 → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Tendsto (fun n => ∫ x in torusBox, w n x * ∑ i : Fin 2, u n x i * pd i χ x) l
      (𝓝 (∫ x in torusBox, z x * ∑ i : Fin 2, v x i * pd i χ x)) := by
  have he (a : Lp ℝ 2 μT) (b : L2T) :
      (∫ x in torusBox, a x * ∑ i : Fin 2, b x i * pd i χ x) =
        ∑ i : Fin 2, ∫ x in torusBox, a x * b x i * pd i χ x := by
    simp only [Finset.mul_sum, ← mul_assoc]
    exact integral_finset_sum _ (fun i _ =>
      integrable_scalar_vector_mul b a (contDiff_pd_infty hχ i).continuous i)
  simp_rw [he]
  simp only [Fin.sum_univ_two]
  exact (tendsto_integral_scalar_vector_mul hu hw (contDiff_pd_infty hχ 0).continuous 0).add
    (tendsto_integral_scalar_vector_mul hu hw (contDiff_pd_infty hχ 1).continuous 1)

/-- The actual `L²` div--curl field satisfies the nonlinear spatial
vorticity-to-momentum identity, proved through genuine Fourier approximation. -/
theorem integral_flux_perpGradient {u : L2T} {w : R2 → ℝ}
    (hu : DivFree u) (hw : MemLp w 2 μT) (hc : IsCurl u w)
    {χ : R2 → ℝ} (hχ : IsScalarTest χ) :
    (∫ x in torusBox, ∑ i, ∑ j, u x i * u x j * pd j (perpGradient χ) x i) =
      -(∫ x in torusBox, w x * ∑ i : Fin 2, u x i * pd i χ x) := by
  let V (N : ℕ) := boxVectorFourierPolynomial N u
  let U (N : ℕ) : L2T := (memLp_boxVectorFourierPolynomial N u).toLp (V N)
  let W (N : ℕ) : Lp ℝ 2 μT :=
    (memLp_curl_boxVectorFourierPolynomial N u w hw hc).toLp
      (fun x => pd 0 (V N) x 1 - pd 1 (V N) x 0)
  have hU : Tendsto U atTop (𝓝 u) := tendsto_boxVectorFourierPolynomial_toLp u
  have hW : Tendsto W atTop (𝓝 (hw.toLp w)) :=
    tendsto_curl_boxVectorFourierPolynomial_toLp u w hw hc
  have hUae (N : ℕ) : (U N : R2 → R2) =ᵐ[μT] V N :=
    (memLp_boxVectorFourierPolynomial N u).coeFn_toLp
  have hWae (N : ℕ) : (W N : R2 → ℝ) =ᵐ[μT]
      (fun x => pd 0 (V N) x 1 - pd 1 (V N) x 0) :=
    (memLp_curl_boxVectorFourierPolynomial N u w hw hc).coeFn_toLp
  have he (N : ℕ) :
      (∫ x in torusBox, ∑ i, ∑ j, U N x i * U N x j * pd j (perpGradient χ) x i) =
        -(∫ x in torusBox, W N x * ∑ i : Fin 2, U N x i * pd i χ x) := by
    calc
      _ = ∫ x in torusBox, ∑ i, ∑ j, V N x i * V N x j * pd j (perpGradient χ) x i := by
        apply integral_congr_ae
        filter_upwards [hUae N] with x hx
        rw [hx]
      _ = -(∫ x in torusBox, (pd 0 (V N) x 1 - pd 1 (V N) x 0) *
          ∑ i : Fin 2, V N x i * pd i χ x) :=
        integral_flux_perpGradient_smooth
          ((smooth_periodic_boxVectorFourierPolynomial N u).1.of_le (by simp))
          (smooth_periodic_boxVectorFourierPolynomial N u).2
          (divFree_boxVectorFourierPolynomial N u hu) hχ
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hUae N, hWae N] with x hx hy
        rw [hx, hy]
  have hleft := ((continuous_stationary_pairing (contDiff_perpGradient hχ.1)).tendsto u).comp hU
  have hright := (tendsto_integral_vorticity_transport hU hW hχ.1).neg
  have hright' : Tendsto
      (fun N => ∫ x in torusBox, ∑ i, ∑ j, U N x i * U N x j * pd j (perpGradient χ) x i)
      atTop (𝓝 (-(∫ x in torusBox, hw.toLp w x * ∑ i : Fin 2, u x i * pd i χ x))) :=
    hright.congr' (Eventually.of_forall fun N => (he N).symm)
  have hlim := tendsto_nhds_unique hleft hright'
  rw [hlim]
  congr 1
  apply integral_congr_ae
  filter_upwards [hw.coeFn_toLp] with x hx
  rw [hx]

lemma integrable_l2_component_continuous (u : L2T) (i : Fin 2)
    {k : R2 → ℝ} (hk : Continuous k) :
    Integrable (fun x => u x i * k x) μT := by
  obtain ⟨C, hC⟩ := bound_on_box hk
  exact integrable_lin u i hk.aestronglyMeasurable hC

lemma integral_dot_constant_of_mean_zero (u : L2T)
    (hmean : ∫ x in torusBox, u x = 0) (c : R2) :
    (∫ x in torusBox, ∑ i : Fin 2, u x i * c i) = 0 := by
  have hc (i : Fin 2) : (∫ x in torusBox, u x i) = 0 := by
    calc
      _ = (EuclideanSpace.proj i : R2 →L[ℝ] ℝ) (∫ x in torusBox, u x) :=
        (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integral_comp_comm
          ((Lp.memLp u).integrable (by norm_num))
      _ = 0 := by rw [hmean]; rfl
  simp only [Fin.sum_univ_two]
  rw [integral_add (integrable_l2_component_continuous u 0 continuous_const)
    (integrable_l2_component_continuous u 1 continuous_const),
    integral_mul_const, integral_mul_const, hc, hc]
  ring

/-- The curl identity controls testing against a stream field; the true
mean-zero normalization removes its constant harmonic part. -/
lemma integral_dot_constant_add_perpGradient {u : L2T} {w : R2 → ℝ}
    (hc : IsCurl u w) (hmean : ∫ x in torusBox, u x = 0)
    {χ : R2 → ℝ} (hχ : IsScalarTest χ) (c : R2) :
    (∫ x in torusBox, ∑ i : Fin 2, u x i * (c + perpGradient χ x) i) =
      -(∫ x in torusBox, w x * χ x) := by
  have hpoint (x : R2) :
      (∑ i : Fin 2, u x i * (c + perpGradient χ x) i) =
        (∑ i : Fin 2, u x i * c i) - (u x 0 * pd 1 χ x - u x 1 * pd 0 χ x) := by
    simp only [Fin.sum_univ_two, PiLp.add_apply, perpGradient_zero, perpGradient_one]
    ring
  have hI : Integrable (fun x => ∑ i : Fin 2, u x i * c i) μT :=
    integrable_finset_sum _ (fun i _ => integrable_l2_component_continuous u i continuous_const)
  have hJ : Integrable (fun x => u x 0 * pd 1 χ x - u x 1 * pd 0 χ x) μT :=
    (integrable_l2_component_continuous u 0 (contDiff_pd_infty hχ.1 1).continuous).sub
      (integrable_l2_component_continuous u 1 (contDiff_pd_infty hχ.1 0).continuous)
  simp_rw [hpoint]
  rw [integral_sub hI hJ, integral_dot_constant_of_mean_zero u hmean c, zero_sub,
    ← hc χ hχ]

lemma integrable_scalar_l2_continuous {w : R2 → ℝ} (hw : MemLp w 2 μT)
    {k : R2 → ℝ} (hk : Continuous k) : Integrable (fun x => w x * k x) μT := by
  obtain ⟨C, hC⟩ := bound_on_box hk
  apply (hw.integrable (by norm_num)).mul_bdd (c := C) hk.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

lemma integrable_vorticity_transport (u : L2T) {w : R2 → ℝ} (hw : MemLp w 2 μT)
    {χ : R2 → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Integrable (fun x => w x * ∑ i : Fin 2, u x i * pd i χ x) μT := by
  have hI : Integrable (fun x => hw.toLp w x * ∑ i : Fin 2, u x i * pd i χ x) μT := by
    simp only [Finset.mul_sum, ← mul_assoc]
    exact integrable_finset_sum _ (fun i _ =>
      integrable_scalar_vector_mul u (hw.toLp w) (contDiff_pd_infty hχ i).continuous i)
  apply hI.congr
  filter_upwards [hw.coeFn_toLp] with x hx
  rw [hx]

lemma eulerTest_stream_slice {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) (t : ℝ) : IsScalarTest (streamFunction (φ t)) := by
  have hs : ContDiff ℝ ∞ (φ t) := hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  exact ⟨contDiff_streamFunction hs (hφ.divFree t),
    isTorusPeriodic_streamFunction hs (hφ.divFree t) (hφ.periodic t)⟩

lemma integral_eulerTest_stream_pairing {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) {u : L2T} {w : R2 → ℝ}
    (hc : IsCurl u w) (hmean : ∫ x in torusBox, u x = 0) (t : ℝ) :
    (∫ x in torusBox, ∑ i : Fin 2, u x i * φ t x i) =
      -(∫ x in torusBox, w x * streamFunction (φ t) x) := by
  calc
    _ = ∫ x in torusBox, ∑ i : Fin 2, u x i *
        (streamConstant (φ t) + perpGradient (streamFunction (φ t)) x) i := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (∑ i : Fin 2, u x i * φ t x i) =
          ∑ i : Fin 2, u x i * (streamConstant (φ t) +
            perpGradient (streamFunction (φ t)) x) i
        rw [(eulerTest_stream_decomposition hφ).2.2.2 t x]
        rfl
    _ = _ := integral_dot_constant_add_perpGradient hc hmean
      (eulerTest_stream_slice hφ t) _

lemma integral_eulerTest_stream_time_pairing {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) {u : L2T} {w : R2 → ℝ}
    (hc : IsCurl u w) (hmean : ∫ x in torusBox, u x = 0) (t : ℝ) :
    (∫ x in torusBox, ∑ i : Fin 2, u x i * deriv (fun s => φ s x i) t) =
      -(∫ x in torusBox, w x * deriv (fun s => streamFunction (φ s) x) t) := by
  let c : R2 := torusVec (deriv (fun s => streamConstant (φ s) 0) t)
    (deriv (fun s => streamConstant (φ s) 1) t)
  calc
    _ = ∫ x in torusBox, ∑ i : Fin 2, u x i *
        (c + perpGradient (fun y => deriv (fun s => streamFunction (φ s) y) t) x) i := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      simp only [Fin.sum_univ_two, PiLp.add_apply, perpGradient_zero, perpGradient_one]
      change u x 0 * deriv (fun s => φ s x 0) t + u x 1 * deriv (fun s => φ s x 1) t =
        u x 0 * (deriv (fun s => streamConstant (φ s) 0) t -
          pd 1 (fun y => deriv (fun s => streamFunction (φ s) y) t) x) +
        u x 1 * (deriv (fun s => streamConstant (φ s) 1) t +
          pd 0 (fun y => deriv (fun s => streamFunction (φ s) y) t) x)
      rw [eulerTest_stream_deriv_zero hφ, eulerTest_stream_deriv_one hφ]
    _ = _ := integral_dot_constant_add_perpGradient hc hmean
      (eulerTest_stream_time_test hφ t) c

lemma integral_eulerTest_stream_flux {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) {u : L2T} {w : R2 → ℝ}
    (hu : DivFree u) (hw : MemLp w 2 μT) (hc : IsCurl u w) (t : ℝ) :
    (∫ x in torusBox, ∑ i, ∑ j, u x i * u x j * pd j (φ t) x i) =
      -(∫ x in torusBox, w x * ∑ i : Fin 2, u x i * pd i (streamFunction (φ t)) x) := by
  have hfield : φ t = fun x => streamConstant (φ t) +
      perpGradient (streamFunction (φ t)) x :=
    funext ((eulerTest_stream_decomposition hφ).2.2.2 t)
  have hpd (j : Fin 2) (x : R2) : pd j (φ t) x =
      pd j (perpGradient (streamFunction (φ t))) x := by
    have he := congrArg (fun f : R2 → R2 => pd j f x) hfield
    simpa only [pd, fderiv_const_add] using he
  simp_rw [hpd]
  exact integral_flux_perpGradient hu hw hc (eulerTest_stream_slice hφ t)

/-- At each actual time, the original Euler integrand is the negative
vorticity-transport test pairing. -/
theorem integral_eulerIntegrand_eq_neg_vorticity {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) {u : L2T} {w : R2 → ℝ}
    (hu : DivFree u) (hw : MemLp w 2 μT) (hc : IsCurl u w)
    (hmean : ∫ x in torusBox, u x = 0) (t : ℝ) :
    (∫ x in torusBox, eulerIntegrand u φ t x) =
      -(∫ x in torusBox, w x *
        (deriv (fun s => streamFunction (φ s) x) t +
          ∑ i : Fin 2, u x i * pd i (streamFunction (φ t)) x)) := by
  have hφ1 : ContDiff ℝ 1 (Function.uncurry φ) := hφ.smooth.of_le (by simp)
  have hItime : Integrable (fun x => ∑ i : Fin 2, u x i * deriv (fun s => φ s x i) t) μT :=
    integrable_finset_sum _ (fun i _ => integrable_l2_component_continuous u i
      ((continuous_deriv_time hφ1 i).comp (continuous_const.prodMk continuous_id)))
  have hIflux : Integrable (fun x => ∑ i, ∑ j, u x i * u x j * pd j (φ t) x i) μT := by
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    have hk : Continuous (fun x => pd j (φ t) x i) :=
      (continuous_pd hφ1 i j).comp (continuous_const.prodMk continuous_id)
    obtain ⟨C, hC⟩ := bound_on_box hk
    exact integrable_bilin u u i j hk.aestronglyMeasurable hC
  have hJtime : Integrable (fun x => w x * deriv (fun s => streamFunction (φ s) x) t) μT :=
    integrable_scalar_l2_continuous hw (eulerTest_stream_time_test hφ t).1.continuous
  have hJflux : Integrable (fun x => w x *
      ∑ i : Fin 2, u x i * pd i (streamFunction (φ t)) x) μT :=
    integrable_vorticity_transport u hw (eulerTest_stream_slice hφ t).1
  unfold eulerIntegrand
  rw [integral_add hItime hIflux, integral_eulerTest_stream_time_pairing hφ hc hmean,
    integral_eulerTest_stream_flux hφ hu hw hc]
  simp_rw [mul_add]
  rw [integral_add hJtime hJflux]
  ring

/-- A genuine space-time weak vorticity equation for every scalar test
implies the original momentum weak equation for every Euler test. All
spatial fields are the actual `L²` fields, with their actual `L²` curls. -/
theorem weakEuler_of_weakVorticity {T : ℝ} (hT : 0 ≤ T)
    {U : ℝ → L2T} {w : ℝ → R2 → ℝ}
    (hU : ContinuousOn U (Icc 0 T))
    (hdiv : ∀ t ∈ Icc 0 T, DivFree (U t))
    (hw : ∀ t ∈ Icc 0 T, MemLp (w t) 2 μT)
    (hc : ∀ t ∈ Icc 0 T, IsCurl (U t) (w t))
    (hmean : ∀ t ∈ Icc 0 T, ∫ x in torusBox, U t x = 0)
    (hweak : ∀ χ : ℝ → R2 → ℝ, IsVorticityTest T χ →
      (∫ t in (0 : ℝ)..T, ∫ x in torusBox, w t x *
        (deriv (fun s => χ s x) t + ∑ i : Fin 2, U t x i * pd i (χ t) x)) +
          (∫ x in torusBox, w 0 x * χ 0 x) = 0) :
    IsWeakEulerSolution T (U 0) U := by
  refine ⟨hU, hdiv, rfl, ?_⟩
  intro φ hφ
  have hχ := eulerTest_streamFunction hφ
  have hvort := hweak (fun t => streamFunction (φ t)) hχ
  have htime : (∫ t in (0 : ℝ)..T, ∫ x in torusBox, eulerIntegrand (U t) φ t x) =
      -(∫ t in (0 : ℝ)..T, ∫ x in torusBox, w t x *
        (deriv (fun s => streamFunction (φ s) x) t +
          ∑ i : Fin 2, U t x i * pd i (streamFunction (φ t)) x)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    exact integral_eulerIntegrand_eq_neg_vorticity hφ (hdiv t ht') (hw t ht')
      (hc t ht') (hmean t ht') t
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  rw [htime, integral_eulerTest_stream_pairing hφ (hc 0 hzero) (hmean 0 hzero) 0]
  linarith [hvort]

theorem weakEuler_of_weakVorticity_with_initial {T : ℝ} (hT : 0 ≤ T)
    {U : ℝ → L2T} {u₀ : L2T} {w : ℝ → R2 → ℝ}
    (hU : ContinuousOn U (Icc 0 T))
    (hdiv : ∀ t ∈ Icc 0 T, DivFree (U t))
    (hw : ∀ t ∈ Icc 0 T, MemLp (w t) 2 μT)
    (hc : ∀ t ∈ Icc 0 T, IsCurl (U t) (w t))
    (hmean : ∀ t ∈ Icc 0 T, ∫ x in torusBox, U t x = 0) (hinit : U 0 = u₀)
    (hweak : ∀ χ : ℝ → R2 → ℝ, IsVorticityTest T χ →
      (∫ t in (0 : ℝ)..T, ∫ x in torusBox, w t x *
        (deriv (fun s => χ s x) t + ∑ i : Fin 2, U t x i * pd i (χ t) x)) +
          (∫ x in torusBox, w 0 x * χ 0 x) = 0) :
    IsWeakEulerSolution T u₀ U := by
  rw [← hinit]
  exact weakEuler_of_weakVorticity hT hU hdiv hw hc hmean hweak

end Euler2D

end
