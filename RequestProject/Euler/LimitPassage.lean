module

public import RequestProject.Euler.Delay

/-!
# Strong limits of weak Euler solutions

The weak Euler equation is closed under uniform convergence in the spatial `L²` norm.
The estimates below keep track of the quadratic term in the weak formulation; no
convergence of pointwise representatives of the velocity is required.
-/

@[expose] public section

open MeasureTheory Real Filter Topology Set
open scoped ContDiff

namespace Euler2D

/-- The quadratic spatial pairing is continuous under strong `L²` convergence. -/
lemma tendsto_integral_bilin {ι : Type*} {l : Filter ι}
    {v w : ι → L2T} {v₀ w₀ : L2T}
    (hv : Tendsto v l (𝓝 v₀)) (hw : Tendsto w l (𝓝 w₀))
    {k : R2 → ℝ} (hk : Continuous k) (i j : Fin 2) :
    Tendsto (fun n => ∫ x in torusBox, v n x i * w n x j * k x) l
      (𝓝 (∫ x in torusBox, v₀ x i * w₀ x j * k x)) := by
  obtain ⟨C, hC⟩ := bound_on_box hk
  have hI : ∀ f g : L2T, Integrable (fun x => f x i * g x j * k x) μT :=
    fun f g => integrable_bilin f g i j hk.aestronglyMeasurable hC
  have hdecomp : ∀ n,
      (∫ x in torusBox, v n x i * w n x j * k x) -
        ∫ x in torusBox, v₀ x i * w₀ x j * k x =
      (∫ x in torusBox, (v n - v₀) x i * w n x j * k x) +
        ∫ x in torusBox, v₀ x i * (w n - w₀) x j * k x := by
    intro n
    have e1 : (∫ x in torusBox, (v n - v₀) x i * w n x j * k x) =
        (∫ x in torusBox, v n x i * w n x j * k x) -
          ∫ x in torusBox, v₀ x i * w n x j * k x := by
      rw [← integral_sub (hI _ _) (hI _ _)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (v n) v₀] with x hx
      rw [hx]; simp; ring
    have e2 : (∫ x in torusBox, v₀ x i * (w n - w₀) x j * k x) =
        (∫ x in torusBox, v₀ x i * w n x j * k x) -
          ∫ x in torusBox, v₀ x i * w₀ x j * k x := by
      rw [← integral_sub (hI _ _) (hI _ _)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (w n) w₀] with x hx
      rw [hx]; simp; ring
    rw [e1, e2]; ring
  have hvd : Tendsto (fun n => ‖v n - v₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  have hwd : Tendsto (fun n => ‖w n - w₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hw
  have hb : Tendsto (fun n => C * (‖v n - v₀‖ * ‖w n‖) +
      C * (‖v₀‖ * ‖w n - w₀‖)) l (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hvd.mul hw.norm)).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hwd))
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm _ hb
  intro n
  rw [Real.norm_eq_abs, hdecomp n]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_integral_bilin_le (v n - v₀) (w n) i j hC)
    (abs_integral_bilin_le v₀ (w n - w₀) i j hC))

/-- The linear spatial pairing is continuous under strong `L²` convergence. -/
lemma tendsto_integral_lin {ι : Type*} {l : Filter ι} {v : ι → L2T} {v₀ : L2T}
    (hv : Tendsto v l (𝓝 v₀)) {k : R2 → ℝ} (hk : Continuous k) (i : Fin 2) :
    Tendsto (fun n => ∫ x in torusBox, v n x i * k x) l
      (𝓝 (∫ x in torusBox, v₀ x i * k x)) := by
  have h := tendsto_integral_bilin hv (tendsto_const_nhds (x := constE0)) hk i 0
  have he : ∀ f : L2T, (∫ x in torusBox, f x i * constE0 x 0 * k x) =
      ∫ x in torusBox, f x i * k x := by
    intro f
    apply integral_congr_ae
    filter_upwards [constE0_ae] with x hx
    rw [hx, mul_one]
  simpa only [he] using h

/-- Strong `L²` limits preserve the distributional divergence constraint. -/
theorem divFree_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {v : ι → L2T} {v₀ : L2T} (hv : Tendsto v l (𝓝 v₀))
    (hdiv : ∀ᶠ n in l, DivFree (v n)) : DivFree v₀ := by
  intro ψ hψ
  have hpd : ∀ i : Fin 2, Continuous (pd i ψ) := by
    intro i
    exact (hψ.1.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 ψ).continuous_fderiv
      one_ne_zero |>.clm_apply continuous_const
  have hi : ∀ f : L2T, (∫ x in torusBox, ∑ i, f x i * pd i ψ x) =
      ∑ i, ∫ x in torusBox, f x i * pd i ψ x := by
    intro f
    apply integral_finset_sum
    intro i _
    obtain ⟨C, hC⟩ := bound_on_box (hpd i)
    exact integrable_lin f i (hpd i).aestronglyMeasurable hC
  have ht : Tendsto (fun n => ∫ x in torusBox, ∑ i, v n x i * pd i ψ x) l
      (𝓝 (∫ x in torusBox, ∑ i, v₀ x i * pd i ψ x)) := by
    simp_rw [hi]
    simp only [Fin.sum_univ_two]
    exact (tendsto_integral_lin hv (hpd 0) 0).add (tendsto_integral_lin hv (hpd 1) 1)
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hdiv.mono fun n hn =>
    (hn ψ hψ).symm))

/-- A convenient linear version of the spatial pairing estimate. -/
lemma abs_integral_lin_le (v : L2T) (i : Fin 2) {k : R2 → ℝ} {C : ℝ}
    (hC : ∀ x ∈ torusBox, |k x| ≤ C) :
    |∫ x in torusBox, v x i * k x| ≤ C * (‖v‖ * ‖constE0‖) := by
  have he : (∫ x in torusBox, v x i * constE0 x 0 * k x) =
      ∫ x in torusBox, v x i * k x := by
    apply integral_congr_ae
    filter_upwards [constE0_ae] with x hx
    rw [hx, mul_one]
  simpa only [he] using abs_integral_bilin_le v constE0 i 0 hC

/-- Uniform spatial bounds for a continuous kernel on a compact time interval. -/
lemma bound_on_time_box (T : ℝ) {k : ℝ → R2 → ℝ}
    (hk : Continuous (Function.uncurry k)) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x ∈ torusBox, |k t x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_closedBox).exists_bound_of_continuousOn
    hk.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht x hx => ?_⟩
  have hb : |k t x| ≤ C := by
    simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs] using
      (hC (t, x) ⟨ht, torusBox_subset_closedBox hx⟩)
  exact hb.trans (le_max_left _ _)

/-- A bounded family of velocities gives bounded weak-formulation integrands. -/
lemma eulerIntegral_uniform_bound {φ : ℝ → R2 → R2}
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (T M : ℝ) (hM : 0 ≤ M) :
    ∃ K, ∀ t ∈ Icc 0 T, ∀ v : L2T, ‖v‖ ≤ M →
      |∫ x in torusBox, eulerIntegrand v φ t x| ≤ K := by
  obtain ⟨C₀, hC₀, b₀⟩ := bound_on_time_box T (continuous_deriv_time hφ 0)
  obtain ⟨C₁, hC₁, b₁⟩ := bound_on_time_box T (continuous_deriv_time hφ 1)
  obtain ⟨D₀₀, hD₀₀, b₀₀⟩ := bound_on_time_box T (continuous_pd hφ 0 0)
  obtain ⟨D₀₁, hD₀₁, b₀₁⟩ := bound_on_time_box T (continuous_pd hφ 0 1)
  obtain ⟨D₁₀, hD₁₀, b₁₀⟩ := bound_on_time_box T (continuous_pd hφ 1 0)
  obtain ⟨D₁₁, hD₁₁, b₁₁⟩ := bound_on_time_box T (continuous_pd hφ 1 1)
  refine ⟨C₀ * (M * ‖constE0‖) + C₁ * (M * ‖constE0‖) +
    ((D₀₀ * (M * M) + D₀₁ * (M * M)) +
      (D₁₀ * (M * M) + D₁₁ * (M * M))), ?_⟩
  intro t ht v hv
  rw [integral_eulerIntegrand_eq hφ]
  simp only [Fin.sum_univ_two]
  have b1 := abs_integral_lin_le v 0 (b₀ t ht)
  have b2 := abs_integral_lin_le v 1 (b₁ t ht)
  have b3 := abs_integral_bilin_le v v 0 0 (b₀₀ t ht)
  have b4 := abs_integral_bilin_le v v 0 1 (b₀₁ t ht)
  have b5 := abs_integral_bilin_le v v 1 0 (b₁₀ t ht)
  have b6 := abs_integral_bilin_le v v 1 1 (b₁₁ t ht)
  calc
    |(_ + _) + ((_ + _) + (_ + _))| ≤
        (C₀ * (‖v‖ * ‖constE0‖) + C₁ * (‖v‖ * ‖constE0‖)) +
        ((D₀₀ * (‖v‖ * ‖v‖) + D₀₁ * (‖v‖ * ‖v‖)) +
          (D₁₀ * (‖v‖ * ‖v‖) + D₁₁ * (‖v‖ * ‖v‖))) := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add b1 b2))
        ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add b3 b4))
          ((abs_add_le _ _).trans (add_le_add b5 b6)))))
    _ ≤ _ := by gcongr

/-- Pointwise continuity of the weak-formulation integrand in the spatial `L²` norm. -/
lemma tendsto_eulerIntegral {ι : Type*} {l : Filter ι} {v : ι → L2T} {v₀ : L2T}
    (hv : Tendsto v l (𝓝 v₀)) {φ : ℝ → R2 → R2}
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (t : ℝ) :
    Tendsto (fun n => ∫ x in torusBox, eulerIntegrand (v n) φ t x) l
      (𝓝 (∫ x in torusBox, eulerIntegrand v₀ φ t x)) := by
  simp_rw [integral_eulerIntegrand_eq hφ]
  simp only [Fin.sum_univ_two]
  have hlin := fun i => tendsto_integral_lin hv
    ((continuous_deriv_time hφ i).comp (Continuous.prodMk_right t)) i
  have hbilin := fun i j => tendsto_integral_bilin hv hv
    ((continuous_pd hφ i j).comp (Continuous.prodMk_right t)) i j
  exact ((hlin 0).add (hlin 1)).add
    (((hbilin 0 0).add (hbilin 0 1)).add ((hbilin 1 0).add (hbilin 1 1)))

/-- The weak-formulation integrand is continuous along a path continuous on `[0,T]`. -/
lemma continuousOn_eulerIntegral {T : ℝ} (hT : 0 ≤ T) {u : ℝ → L2T}
    (hu : ContinuousOn u (Icc 0 T)) {φ : ℝ → R2 → R2}
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ContinuousOn (fun t => ∫ x in torusBox, eulerIntegrand (u t) φ t x) (Icc 0 T) := by
  have he : Continuous (fun t => ∫ x in torusBox,
      eulerIntegrand (extendPath hT u t) φ t x) :=
    continuous_iff_continuousAt.2 fun t => continuousAt_eulerIntegral hφ
      (extendPath_continuous hT hu).continuousAt
  exact he.continuousOn.congr fun t ht =>
    congrArg (fun v : L2T => ∫ x in torusBox, eulerIntegrand v φ t x)
      (extendPath_eq hT u ht).symm

/-- Uniform strong convergence permits passing to the limit in the time-integrated Euler
nonlinearity. -/
theorem tendsto_time_eulerIntegral {T : ℝ} (hT : 0 ≤ T)
    {U : ℕ → ℝ → L2T} {u : ℝ → L2T}
    (hU : ∀ n, ContinuousOn (U n) (Icc 0 T))
    (hlim : TendstoUniformlyOn U u atTop (Icc 0 T))
    {φ : ℝ → R2 → R2} (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..T, ∫ x in torusBox,
      eulerIntegrand (U n t) φ t x) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ x in torusBox, eulerIntegrand (u t) φ t x)) := by
  have hu : ContinuousOn u (Icc 0 T) :=
    hlim.continuousOn (Eventually.of_forall hU).frequently
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  set M := max B 0 + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hUb : ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, ‖U n t‖ ≤ M := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim 1 one_pos] with n hn t ht
    have hd : ‖U n t - u t‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hn t ht
    have hb := hB t ht
    have hh := norm_le_insert' (U n t) (u t)
    dsimp [M]
    linarith [le_max_left B 0]
  obtain ⟨K, hK⟩ := eulerIntegral_uniform_bound hφ T M hM
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 ((measure_mono Ioc_subset_Icc_self).trans_lt
      isCompact_Icc.measure_lt_top).ne
  simp only [intervalIntegral.integral_of_le hT]
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun n =>
      ((continuousOn_eulerIntegral hT (hU n) hφ).intervalIntegrable_of_Icc hT).1.aestronglyMeasurable
  · refine ⟨K, hUb.mono fun n hn => ?_⟩
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun t ht => by
      simpa only [Real.norm_eq_abs] using hK t ⟨ht.1.le, ht.2⟩ (U n t) (hn t ⟨ht.1.le, ht.2⟩)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun t ht =>
      tendsto_eulerIntegral (hlim.tendsto_at ⟨ht.1.le, ht.2⟩) hφ t

/-- Uniform strong `L²` limits of weak Euler solutions are weak Euler solutions.  The
initial data may vary and are only required to converge strongly in `L²`. -/
theorem isWeakEulerSolution_of_tendstoUniformlyOn {T : ℝ} (hT : 0 ≤ T)
    {U : ℕ → ℝ → L2T} {u : ℝ → L2T} {u₀n : ℕ → L2T} {u₀ : L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀n n) (U n))
    (hlim : TendstoUniformlyOn U u atTop (Icc 0 T))
    (hinit : Tendsto u₀n atTop (𝓝 u₀)) : IsWeakEulerSolution T u₀ u where
  continuous := hlim.continuousOn (Eventually.of_forall fun n => (hU n).continuous).frequently
  divFree t ht := divFree_of_tendsto (hlim.tendsto_at ht)
    (Eventually.of_forall fun n => (hU n).divFree t ht)
  initial := by
    have ht := hlim.tendsto_at (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
    have he : (fun n => U n 0) = u₀n := funext fun n => (hU n).initial
    rw [he] at ht
    exact (tendsto_nhds_unique ht hinit)
  weak φ hφ := by
    have hi : Tendsto (fun n => ∫ x in torusBox, ∑ i, u₀n n x i * φ 0 x i) atTop
        (𝓝 (∫ x in torusBox, ∑ i, u₀ x i * φ 0 x i)) := by
      simp_rw [lin_sum_integral hφ.contDiff_one]
      simp only [Fin.sum_univ_two]
      have hk : ∀ i : Fin 2, Continuous (fun x => φ 0 x i) := fun i =>
        (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
          (hφ.contDiff_one.continuous.comp (Continuous.prodMk_right 0))
      exact (tendsto_integral_lin hinit (hk 0) 0).add
        (tendsto_integral_lin hinit (hk 1) 1)
    have he := (tendsto_time_eulerIntegral hT (fun n => (hU n).continuous)
      hlim hφ.contDiff_one).add hi
    exact tendsto_nhds_unique he (tendsto_const_nhds.congr' (Eventually.of_forall
      fun n => ((hU n).weak φ hφ).symm))

/-- A uniform lower bound on departure from a convergent datum survives both a uniform
limit of paths and a convergent choice of observation times. -/
theorem departure_lowerBound_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι} [NeBot l]
    {T c : ℝ} {U : ι → ℝ → L2T} {u : ℝ → L2T}
    {v₀n : ι → L2T} {v₀ : L2T} {τ : ι → ℝ} {t : ℝ}
    (hu : ContinuousOn u (Icc 0 T))
    (hlim : TendstoUniformlyOn U u l (Icc 0 T))
    (hv₀ : Tendsto v₀n l (𝓝 v₀)) (hτ : Tendsto τ l (𝓝 t))
    (hτI : ∀ᶠ n in l, τ n ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hbound : ∀ᶠ n in l, c ≤ ‖U n (τ n) - v₀n n‖) :
    c ≤ ‖u t - v₀‖ := by
  have htend : Tendsto (fun n => U n (τ n)) l (𝓝 (u t)) :=
    hlim.tendsto_comp (hu t ht) (tendsto_nhdsWithin_iff.mpr ⟨hτ, hτI⟩)
  exact ge_of_tendsto (htend.sub hv₀).norm hbound

/-- A positive lower bound prevents the limiting path from being the constant datum. -/
theorem departure_ne_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι} [NeBot l]
    {T c : ℝ} {U : ι → ℝ → L2T} {u : ℝ → L2T}
    {v₀n : ι → L2T} {v₀ : L2T} {τ : ι → ℝ} {t : ℝ}
    (hc : 0 < c) (hu : ContinuousOn u (Icc 0 T))
    (hlim : TendstoUniformlyOn U u l (Icc 0 T))
    (hv₀ : Tendsto v₀n l (𝓝 v₀)) (hτ : Tendsto τ l (𝓝 t))
    (hτI : ∀ᶠ n in l, τ n ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hbound : ∀ᶠ n in l, c ≤ ‖U n (τ n) - v₀n n‖) : u t ≠ v₀ := by
  have hb := departure_lowerBound_of_tendstoUniformlyOn hu hlim hv₀ hτ hτI ht hbound
  exact sub_ne_zero.mp (norm_pos_iff.mp (hc.trans_le hb))

/-- Compactness of the observation times supplies a limiting departure time, without
requiring that the original sequence of times converges. -/
theorem exists_departure_lowerBound_of_tendstoUniformlyOn
    {T a b c : ℝ} {U : ℕ → ℝ → L2T} {u : ℝ → L2T}
    {v₀n : ℕ → L2T} {v₀ : L2T} {τ : ℕ → ℝ}
    (ha : 0 ≤ a) (hb : b ≤ T) (hu : ContinuousOn u (Icc 0 T))
    (hlim : TendstoUniformlyOn U u atTop (Icc 0 T))
    (hv₀ : Tendsto v₀n atTop (𝓝 v₀))
    (hτ : ∀ n, τ n ∈ Icc a b) (hbound : ∀ n, c ≤ ‖U n (τ n) - v₀n n‖) :
    ∃ t ∈ Icc a b, c ≤ ‖u t - v₀‖ := by
  obtain ⟨t, ht, σ, hσ, hτσ⟩ := isCompact_Icc.tendsto_subseq hτ
  refine ⟨t, ht, departure_lowerBound_of_tendstoUniformlyOn hu
    (hlim.seq_tendstoUniformlyOn σ hσ.tendsto_atTop)
    (hv₀.comp hσ.tendsto_atTop) hτσ ?_ ⟨ha.trans ht.1, ht.2.trans hb⟩ ?_⟩
  · exact Eventually.of_forall fun n => ⟨ha.trans (hτ (σ n)).1, (hτ (σ n)).2.trans hb⟩
  · exact Eventually.of_forall fun n => hbound (σ n)

end Euler2D

end
