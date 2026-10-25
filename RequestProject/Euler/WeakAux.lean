module

public import RequestProject.Euler.Basic

/-!
# Auxiliary estimates for weak Euler solutions

Technical lemmas on the space `L²(𝕋²)` used to manipulate the weak formulation:
`L²` bilinear estimates, continuity in time of the weak-formulation integrands along a
continuous `L²`-valued path, and the time-integrated pairing with `∂ₜφ`.
-/

@[expose] public section

open MeasureTheory Real Filter Topology Set
open scoped ContDiff

namespace Euler2D

/-- The closed square `[0,2π]²`. -/
def closedBox : Set R2 := {x | ∀ i, x i ∈ Icc 0 (2 * π)}

lemma torusBox_subset_closedBox : torusBox ⊆ closedBox :=
  fun _ hx i => Ico_subset_Icc_self (hx i)

lemma isCompact_closedBox : IsCompact closedBox := by
  have : closedBox = (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' (univ.pi fun _ => Icc 0 (2 * π)) := by
    ext x
    simp only [closedBox, mem_setOf_eq, mem_image, Set.mem_pi]
    constructor
    · intro hx; exact ⟨WithLp.equiv 2 _ x, fun i _ => hx i, by simp⟩
    · rintro ⟨y, hy, rfl⟩ i; simpa using hy i (mem_univ _)
  rw [this]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

lemma measurableSet_torusBox : MeasurableSet torusBox := by
  have : torusBox = ⋂ i : Fin 2, (fun x : R2 => x i) ⁻¹' Ico 0 (2 * π) := by
    ext x; simp [torusBox]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage (by fun_prop)

instance : IsFiniteMeasure μT :=
  isFiniteMeasure_restrict.2 (measure_mono torusBox_subset_closedBox |>.trans_lt
    isCompact_closedBox.measure_lt_top).ne


lemma l2_integral_norm_sq (f : L2T) : ∫ x in torusBox, ‖f x‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (f : L2T), MeasureTheory.L2.inner_def]
  congr 1; funext x; rw [real_inner_self_eq_norm_sq]

lemma l2_memLp_norm (f : L2T) : MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) μT := by
  simpa using (Lp.memLp f).norm

lemma l2_integral_mul_norm_le (f g : L2T) :
    ∫ x in torusBox, ‖f x‖ * ‖g x‖ ≤ ‖f‖ * ‖g‖ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μT) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall fun x => norm_nonneg (f x))
    (Filter.Eventually.of_forall fun x => norm_nonneg (g x)) (l2_memLp_norm f) (l2_memLp_norm g)
  have e : ∀ h : L2T, (∫ x in torusBox, ‖h x‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) = ‖h‖ := by
    intro h
    simp_rw [Real.rpow_two]
    rw [l2_integral_norm_sq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [e f, e g] at h
  exact h


lemma abs_coord_le (x : R2) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

lemma aestronglyMeasurable_coord (f : L2T) (i : Fin 2) :
    AEStronglyMeasurable (fun x => f x i) μT :=
  Continuous.comp_aestronglyMeasurable (g := fun y : R2 => y i) (by fun_prop)
    (Lp.aestronglyMeasurable f)

lemma zero_mem_torusBox : (0 : R2) ∈ torusBox := fun i => by
  simp; positivity

lemma integrable_norm_mul_norm (f g : L2T) : Integrable (fun x => ‖f x‖ * ‖g x‖) μT := by
  have hf : MemLp (fun x => ‖f x‖) 2 μT := (Lp.memLp f).norm
  have hg : MemLp (fun x => ‖g x‖) 2 μT := (Lp.memLp g).norm
  exact hf.integrable_mul hg

/-- Integrability of `f_i g_j k` for `f, g ∈ L²` and `k` bounded on the box. -/
lemma integrable_bilin (f g : L2T) (i j : Fin 2) {k : R2 → ℝ}
    (hk : AEStronglyMeasurable k μT) {C : ℝ} (hC : ∀ x ∈ torusBox, |k x| ≤ C) :
    Integrable (fun x => f x i * g x j * k x) μT := by
  refine ((integrable_norm_mul_norm f g).const_mul C).mono' ?_ ?_
  · exact ((aestronglyMeasurable_coord f i).mul (aestronglyMeasurable_coord g j)).mul hk
  · rw [ae_restrict_iff' measurableSet_torusBox]
    refine Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have := hC x hx
    have h0 : 0 ≤ |k x| := abs_nonneg _
    calc |f x i| * |g x j| * |k x| ≤ ‖f x‖ * ‖g x‖ * C := by
          gcongr
          · exact abs_coord_le _ _
          · exact abs_coord_le _ _
      _ = C * (‖f x‖ * ‖g x‖) := by ring

/-- The bilinear estimate `|∫ f_i g_j k| ≤ C ‖f‖ ‖g‖` if `|k| ≤ C` on the box. -/
lemma abs_integral_bilin_le (f g : L2T) (i j : Fin 2) {k : R2 → ℝ} {C : ℝ}
    (hC : ∀ x ∈ torusBox, |k x| ≤ C) :
    |∫ x in torusBox, f x i * g x j * k x| ≤ C * (‖f‖ * ‖g‖) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 zero_mem_torusBox)
  calc |∫ x in torusBox, f x i * g x j * k x|
      ≤ ∫ x in torusBox, |f x i * g x j * k x| := abs_integral_le_integral_abs
    _ ≤ ∫ x in torusBox, C * (‖f x‖ * ‖g x‖) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          ((integrable_norm_mul_norm f g).const_mul C)
        rw [EventuallyLE, ae_restrict_iff' measurableSet_torusBox]
        refine Eventually.of_forall fun x hx => ?_
        rw [abs_mul, abs_mul]
        calc |f x i| * |g x j| * |k x| ≤ ‖f x‖ * ‖g x‖ * C := by
              gcongr
              · exact abs_coord_le _ _
              · exact abs_coord_le _ _
              · exact hC x hx
          _ = C * (‖f x‖ * ‖g x‖) := by ring
    _ = C * ∫ x in torusBox, ‖f x‖ * ‖g x‖ := integral_const_mul _ _
    _ ≤ C * (‖f‖ * ‖g‖) := mul_le_mul_of_nonneg_left (l2_integral_mul_norm_le f g) hC0


lemma uniform_close {k : ℝ → R2 → ℝ} (hk : Continuous (Function.uncurry k)) (s₀ : ℝ) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ t in 𝓝 s₀, ∀ x ∈ torusBox, |k t x - k s₀ x| ≤ η := by
  haveI : CompactSpace closedBox := isCompact_iff_compactSpace.mp isCompact_closedBox
  set f : ℝ → closedBox → ℝ := fun t y => k t y
  have hf : Continuous (Function.uncurry f) :=
    hk.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hu := Continuous.tendstoUniformly f hf s₀
  rw [Metric.tendstoUniformly_iff] at hu
  filter_upwards [hu η hη] with t ht x hx
  have := ht ⟨x, torusBox_subset_closedBox hx⟩
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this.le

lemma bound_on_box {k : R2 → ℝ} (hk : Continuous k) : ∃ C, ∀ x ∈ torusBox, |k x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_closedBox.exists_bound_of_continuousOn hk.continuousOn
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x (torusBox_subset_closedBox hx)⟩

/-- Continuity in time of `t ↦ ∫ (v t)_i (w t)_j k(t,·)` along continuous `L²` paths. -/
lemma continuousAt_bilin {v w : ℝ → L2T} {s₀ : ℝ} (hv : ContinuousAt v s₀)
    (hw : ContinuousAt w s₀) {k : ℝ → R2 → ℝ} (hk : Continuous (Function.uncurry k))
    (i j : Fin 2) :
    ContinuousAt (fun t => ∫ x in torusBox, v t x i * w t x j * k t x) s₀ := by
  have hkt : ∀ t, Continuous (k t) := fun t => hk.comp (Continuous.prodMk_right t)
  have hkm : ∀ t, AEStronglyMeasurable (k t) μT := fun t => (hkt t).aestronglyMeasurable
  obtain ⟨C, hC⟩ := bound_on_box (hkt s₀)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 zero_mem_torusBox)
  have hI : ∀ (f g : L2T) (t : ℝ), Integrable (fun x => f x i * g x j * k t x) μT := by
    intro f g t
    obtain ⟨Ct, hCt⟩ := bound_on_box (hkt t)
    exact integrable_bilin f g i j (hkm t) hCt
  -- decomposition of the difference
  have hdecomp : ∀ t, (∫ x in torusBox, v t x i * w t x j * k t x) -
      ∫ x in torusBox, v s₀ x i * w s₀ x j * k s₀ x =
      (∫ x in torusBox, v t x i * w t x j * (k t x - k s₀ x)) +
      (∫ x in torusBox, (v t - v s₀) x i * w t x j * k s₀ x) +
      (∫ x in torusBox, v s₀ x i * (w t - w s₀) x j * k s₀ x) := by
    intro t
    have e1 : (∫ x in torusBox, v t x i * w t x j * (k t x - k s₀ x)) =
        (∫ x in torusBox, v t x i * w t x j * k t x) -
          ∫ x in torusBox, v t x i * w t x j * k s₀ x := by
      rw [← integral_sub (hI _ _ t) (hI _ _ s₀)]; congr 1; funext x; ring
    have e2 : (∫ x in torusBox, (v t - v s₀) x i * w t x j * k s₀ x) =
        (∫ x in torusBox, v t x i * w t x j * k s₀ x) -
          ∫ x in torusBox, v s₀ x i * w t x j * k s₀ x := by
      rw [← integral_sub (hI _ _ s₀) (hI _ _ s₀)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (v t) (v s₀)] with x hx
      rw [hx]; simp; ring
    have e3 : (∫ x in torusBox, v s₀ x i * (w t - w s₀) x j * k s₀ x) =
        (∫ x in torusBox, v s₀ x i * w t x j * k s₀ x) -
          ∫ x in torusBox, v s₀ x i * w s₀ x j * k s₀ x := by
      rw [← integral_sub (hI _ _ s₀) (hI _ _ s₀)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (w t) (w s₀)] with x hx
      rw [hx]; simp; ring
    rw [e1, e2, e3]; ring
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set M := ‖v s₀‖ + 1
  set M' := ‖w s₀‖ + 1
  have hM : 0 < M := by positivity
  have hM' : 0 < M' := by positivity
  set η := ε / (3 * (M * M' + 1))
  set δ := ε / (3 * (C + 1) * (M + M' + 1))
  have hη : 0 < η := by positivity
  have hδ : 0 < δ := by positivity
  have hv1 : ∀ᶠ t in 𝓝 s₀, ‖v t - v s₀‖ < min δ 1 := by
    have := (Metric.tendsto_nhds.mp hv) (min δ 1) (lt_min hδ one_pos)
    simpa [dist_eq_norm] using this
  have hw1 : ∀ᶠ t in 𝓝 s₀, ‖w t - w s₀‖ < min δ 1 := by
    have := (Metric.tendsto_nhds.mp hw) (min δ 1) (lt_min hδ one_pos)
    simpa [dist_eq_norm] using this
  filter_upwards [hv1, hw1, uniform_close hk s₀ hη] with t ht1 ht2 ht3
  rw [Real.dist_eq, hdecomp]
  have hvt : ‖v t‖ ≤ M := by
    have := norm_le_norm_add_norm_sub' (v t) (v s₀)
    have : ‖v t - v s₀‖ < 1 := lt_of_lt_of_le ht1 (min_le_right _ _)
    simp only [M]; linarith [norm_sub_rev (v t) (v s₀), norm_le_insert' (v t) (v s₀)]
  have hwt : ‖w t‖ ≤ M' := by
    have : ‖w t - w s₀‖ < 1 := lt_of_lt_of_le ht2 (min_le_right _ _)
    simp only [M']; linarith [norm_le_insert' (w t) (w s₀)]
  have b1 := abs_integral_bilin_le (v t) (w t) i j (k := fun x => k t x - k s₀ x) ht3
  have b2 := abs_integral_bilin_le (v t - v s₀) (w t) i j hC
  have b3 := abs_integral_bilin_le (v s₀) (w t - w s₀) i j hC
  have hd1 : ‖v t - v s₀‖ ≤ δ := (lt_of_lt_of_le ht1 (min_le_left _ _)).le
  have hd2 : ‖w t - w s₀‖ ≤ δ := (lt_of_lt_of_le ht2 (min_le_left _ _)).le
  have hvs : ‖v s₀‖ ≤ M := by simp only [M]; linarith
  calc |_ + _ + _| ≤ η * (‖v t‖ * ‖w t‖) + C * (‖v t - v s₀‖ * ‖w t‖) +
        C * (‖v s₀‖ * ‖w t - w s₀‖) := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add b1 b2)) b3)
    _ ≤ η * (M * M') + C * (δ * M') + C * (M * δ) := by
        gcongr
    _ < ε := by
        have e1 : η * (M * M') < ε / 3 := by
          simp only [η]
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_pos hM hM']
        have e2 : C * (δ * M') + C * (M * δ) ≤ 2 * ε / 3 := by
          have : C * (δ * M') + C * (M * δ) = C * (M + M') * δ := by ring
          rw [this]
          simp only [δ]
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hC0 (add_pos hM hM').le]
        linarith


/-- The constant field `e₀` as an element of `L²(𝕋²)`. -/
noncomputable def constE0 : L2T := (memLp_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).toLp _

lemma constE0_ae : ∀ᵐ x ∂μT, constE0 x 0 = 1 := by
  filter_upwards [MemLp.coeFn_toLp (memLp_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
    (μ := μT) (p := 2)] with x hx
  rw [constE0, hx]; simp

/-- Continuity in time of `t ↦ ∫ (v t)_i k(t,·)`. -/
lemma continuousAt_lin {v : ℝ → L2T} {s₀ : ℝ} (hv : ContinuousAt v s₀)
    {k : ℝ → R2 → ℝ} (hk : Continuous (Function.uncurry k)) (i : Fin 2) :
    ContinuousAt (fun t => ∫ x in torusBox, v t x i * k t x) s₀ := by
  have h := continuousAt_bilin hv (continuousAt_const (y := constE0)) hk i 0
  refine h.congr (Eventually.of_forall fun t => ?_)
  apply integral_congr_ae
  filter_upwards [constE0_ae] with x hx
  rw [hx, mul_one]

lemma integrable_lin (f : L2T) (i : Fin 2) {k : R2 → ℝ} (hk : AEStronglyMeasurable k μT)
    {C : ℝ} (hC : ∀ x ∈ torusBox, |k x| ≤ C) : Integrable (fun x => f x i * k x) μT := by
  refine (integrable_bilin f constE0 i 0 hk hC).congr ?_
  filter_upwards [constE0_ae] with x hx
  rw [hx, mul_one]

variable {φ : ℝ → R2 → R2}

lemma hasDerivAt_time (hφ : Differentiable ℝ (Function.uncurry φ)) (t : ℝ) (x : R2) :
    HasDerivAt (fun s => φ s x) (fderiv ℝ (Function.uncurry φ) (t, x) (1, 0)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : R2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (hφ (t, x)).hasFDerivAt.comp_hasDerivAt t h1

lemma deriv_time_coord (hφ : Differentiable ℝ (Function.uncurry φ)) (t : ℝ) (x : R2)
    (i : Fin 2) :
    deriv (fun s => φ s x i) t = fderiv ℝ (Function.uncurry φ) (t, x) (1, 0) i := by
  have := (hasDerivAt_time hφ t x)
  have h2 := (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t this
  exact h2.deriv

lemma pd_eq_fderiv (hφ : Differentiable ℝ (Function.uncurry φ)) (t : ℝ) (x : R2) (j : Fin 2) :
    pd j (φ t) x = fderiv ℝ (Function.uncurry φ) (t, x) (0, EuclideanSpace.single j 1) := by
  have h1 : HasFDerivAt (fun y : R2 => (t, y)) (ContinuousLinearMap.inr ℝ ℝ R2) x :=
    hasFDerivAt_prodMk_right t x
  have h2 := (hφ (t, x)).hasFDerivAt.comp x h1
  unfold pd
  rw [show φ t = Function.uncurry φ ∘ (fun y : R2 => (t, y)) from rfl, h2.fderiv]
  rfl

lemma continuous_deriv_time (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (i : Fin 2) :
    Continuous (Function.uncurry fun t x => deriv (fun s => φ s x i) t) := by
  have hd := hφ.differentiable one_ne_zero
  have hc := hφ.continuous_fderiv one_ne_zero
  have : (Function.uncurry fun t x => deriv (fun s => φ s x i) t) =
      fun p : ℝ × R2 => fderiv ℝ (Function.uncurry φ) p (1, 0) i := by
    funext p; exact deriv_time_coord hd p.1 p.2 i
  rw [this]
  exact (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp (hc.clm_apply continuous_const)

lemma continuous_pd (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (i j : Fin 2) :
    Continuous (Function.uncurry fun t x => pd j (φ t) x i) := by
  have hd := hφ.differentiable one_ne_zero
  have hc := hφ.continuous_fderiv one_ne_zero
  have : (Function.uncurry fun t x => pd j (φ t) x i) =
      fun p : ℝ × R2 => fderiv ℝ (Function.uncurry φ) p (0, EuclideanSpace.single j 1) i := by
    funext p; simp only [Function.uncurry]; rw [pd_eq_fderiv hd]
  rw [this]
  exact (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp (hc.clm_apply continuous_const)

/-- The weak-formulation integral `∫ [v·∂ₜφ + (v⊗v):∇φ](t)` as a sum of elementary integrals. -/
lemma integral_eulerIntegrand_eq (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (v : L2T) (t : ℝ) :
    ∫ x in torusBox, eulerIntegrand v φ t x =
      (∑ i, ∫ x in torusBox, v x i * deriv (fun s => φ s x i) t) +
        ∑ i, ∑ j, ∫ x in torusBox, v x i * v x j * pd j (φ t) x i := by
  have hk1 : ∀ i, Continuous fun x => deriv (fun s => φ s x i) t := fun i =>
    (continuous_deriv_time hφ i).comp (Continuous.prodMk_right t)
  have hk2 : ∀ i j, Continuous fun x => pd j (φ t) x i := fun i j =>
    (continuous_pd hφ i j).comp (Continuous.prodMk_right t)
  have I1 : ∀ i, Integrable (fun x => v x i * deriv (fun s => φ s x i) t) μT := fun i => by
    obtain ⟨C, hC⟩ := bound_on_box (hk1 i)
    exact integrable_lin v i (hk1 i).aestronglyMeasurable hC
  have I2 : ∀ i j, Integrable (fun x => v x i * v x j * pd j (φ t) x i) μT := fun i j => by
    obtain ⟨C, hC⟩ := bound_on_box (hk2 i j)
    exact integrable_bilin v v i j (hk2 i j).aestronglyMeasurable hC
  unfold eulerIntegrand
  rw [integral_add (integrable_finset_sum _ fun i _ => I1 i)
    (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => I2 i j),
    integral_finset_sum _ fun i _ => I1 i, integral_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => I2 i j]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => I2 i j]

/-- Continuity in time of the weak-formulation integrand along a continuous `L²` path. -/
lemma continuousAt_eulerIntegral (hφ : ContDiff ℝ 1 (Function.uncurry φ)) {v : ℝ → L2T}
    {s₀ : ℝ} (hv : ContinuousAt v s₀) :
    ContinuousAt (fun t => ∫ x in torusBox, eulerIntegrand (v t) φ t x) s₀ := by
  simp_rw [integral_eulerIntegrand_eq hφ]
  simp only [Fin.sum_univ_two]
  exact ((continuousAt_lin hv (continuous_deriv_time hφ 0) 0).add
    (continuousAt_lin hv (continuous_deriv_time hφ 1) 1)).add
    (((continuousAt_bilin hv hv (continuous_pd hφ 0 0) 0 0).add
      (continuousAt_bilin hv hv (continuous_pd hφ 0 1) 0 1)).add
     ((continuousAt_bilin hv hv (continuous_pd hφ 1 0) 1 0).add
      (continuousAt_bilin hv hv (continuous_pd hφ 1 1) 1 1)))


variable {φ : ℝ → R2 → R2}

/-- Time integral of the pairing with `∂ₜφ`: `∫ₐᵇ ∫ v·∂ₜφ = ∫ v·(φ(b) - φ(a))`. -/
lemma integral_time_pairing (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (v : L2T) (i : Fin 2)
    (a b : ℝ) :
    ∫ t in a..b, ∫ x in torusBox, v x i * deriv (fun s => φ s x i) t =
      ∫ x in torusBox, v x i * (φ b x i - φ a x i) := by
  set k : ℝ → R2 → ℝ := fun t x => deriv (fun s => φ s x i) t
  have hk : Continuous (Function.uncurry k) := continuous_deriv_time hφ i
  -- a bound for `k` on the compact set `[a,b]×[0,2π]²`
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod isCompact_closedBox).exists_bound_of_continuousOn
    hk.continuousOn
  have hvi : Integrable (fun x => v x i) μT := by
    refine (integrable_norm_mul_norm v constE0).mono' (aestronglyMeasurable_coord v i) ?_
    filter_upwards [constE0_ae] with x hx
    have h1 : ‖constE0 x‖ ≥ 1 := by
      have := abs_coord_le (constE0 x) 0
      rw [hx] at this; simpa using this
    rw [Real.norm_eq_abs]
    calc |v x i| ≤ ‖v x‖ := abs_coord_le _ _
      _ ≤ ‖v x‖ * ‖constE0 x‖ := le_mul_of_one_le_right (norm_nonneg _) h1
  have hint : Integrable (Function.uncurry fun t x => v x i * k t x)
      ((volume.restrict (uIoc a b)).prod μT) := by
    have hprod : Integrable (fun z : ℝ × R2 => C * |v z.2 i|)
        ((volume.restrict (uIoc a b)).prod μT) := by
      haveI : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
        isFiniteMeasure_restrict.2 ((measure_mono uIoc_subset_uIcc).trans_lt
          isCompact_uIcc.measure_lt_top).ne
      have h1 : Integrable (fun _ : ℝ => C) (volume.restrict (uIoc a b)) :=
        integrable_const C
      exact h1.mul_prod hvi.abs
    refine hprod.mono' ?_ ?_
    · apply AEStronglyMeasurable.mul
      · exact (aestronglyMeasurable_coord v i).comp_snd
      · exact hk.aestronglyMeasurable
    · have hmeas : MeasurableSet (uIoc a b ×ˢ torusBox) :=
        measurableSet_uIoc.prod measurableSet_torusBox
      have : ∀ᵐ z ∂((volume.restrict (uIoc a b)).prod μT), z ∈ uIoc a b ×ˢ torusBox := by
        rw [Measure.prod_restrict]
        exact ae_restrict_mem hmeas
      filter_upwards [this] with z hz
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      have := hC (z.1, z.2) ⟨uIoc_subset_uIcc hz.1, torusBox_subset_closedBox hz.2⟩
      rw [Real.norm_eq_abs] at this
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  rw [intervalIntegral_integral_swap hint]
  congr 1; funext x
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hd := hφ.differentiable one_ne_zero
  apply intervalIntegral.integral_deriv_eq_sub
  · intro t _
    exact ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_time hd t x)).differentiableAt
  · exact (hk.comp (Continuous.prodMk_left x)).intervalIntegrable a b

end Euler2D

end
