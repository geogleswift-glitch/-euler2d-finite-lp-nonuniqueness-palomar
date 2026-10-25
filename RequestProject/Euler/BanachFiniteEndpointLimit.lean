module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Topology.MetricSpace.Cauchy

/-! A bounded actual time derivative gives a genuine Banach-space
endpoint limit. No compactness of a bounded Banach ball is assumed. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_left_limit_of_bounded_derivative {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    {α α' : ℝ → E}
    (hd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt α (α' t) t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) T, ‖α' t‖ ≤ M) :
    ∃ a : E, Tendsto α (𝓝[<] T) (𝓝 a) ∧
      ∀ s ∈ Ioo (0 : ℝ) T, ‖α s - a‖ ≤ M * (T - s) := by
  have hdist (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) T) (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) T) :
      dist (α x) (α y) ≤ M * |x - y| := by
    have hh := (convex_Ioo (0 : ℝ) T).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hd t ht).differentiableAt)
      (fun t ht => by rw [(hd t ht).deriv]; exact hb t ht) hy hx
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hh
  have hCauchy : Cauchy (Filter.map α (𝓝[<] T)) := by
    refine Metric.cauchy_iff.mpr ⟨inferInstance, ?_⟩
    intro ε hε
    let δ := min (T / 2) (ε / (4 * (M + 1)))
    have hδ : 0 < δ := lt_min (half_pos hT) (div_pos hε (by positivity))
    have hδT : δ ≤ T / 2 := min_le_left _ _
    have hδε : δ * (4 * (M + 1)) ≤ ε :=
      (le_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp (min_le_right _ _)
    refine ⟨α '' Ioo (T - δ) T, ?_, ?_⟩
    · change α ⁻¹' (α '' Ioo (T - δ) T) ∈ 𝓝[<] T
      filter_upwards [Ioo_mem_nhdsLT (by linarith : T - δ < T)] with t ht
      exact ⟨t, ht, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hx0 : 0 < x := by linarith [hx.1]
      have hy0 : 0 < y := by linarith [hy.1]
      have hxy : |x - y| ≤ 2 * δ := abs_le.mpr ⟨by linarith [hy.2, hx.1], by linarith [hx.2, hy.1]⟩
      exact ((hdist x ⟨hx0, hx.2⟩ y ⟨hy0, hy.2⟩).trans
        (mul_le_mul_of_nonneg_left hxy hM)).trans_lt (by nlinarith)
  obtain ⟨a, ha⟩ := cauchy_map_iff_exists_tendsto.mp hCauchy
  refine ⟨a, ha, ?_⟩
  intro s hs
  have hlim : Tendsto (fun t => ‖α s - α t‖) (𝓝[<] T) (𝓝 ‖α s - a‖) :=
    (tendsto_const_nhds.sub ha).norm
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
  have hh := hdist s hs t ⟨hs.1.trans ht.1, ht.2⟩
  rw [dist_eq_norm, abs_of_neg (sub_neg.mpr ht.1), neg_sub] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le s) hM)

def leftEndpointExtension (α : ℝ → E) (T : ℝ) (a : E) (t : ℝ) : E :=
  if t < T then α t else a

theorem continuousWithinAt_leftEndpointExtension {α : ℝ → E} {T : ℝ} {a : E}
    (ha : Tendsto α (𝓝[<] T) (𝓝 a)) :
    ContinuousWithinAt (leftEndpointExtension α T a) (Iic T) T := by
  have hset : Iic T = insert T (Iio T) := by
    ext t
    simp only [mem_Iic, mem_insert_iff, mem_Iio]
    constructor
    · intro ht
      exact eq_or_lt_of_le ht
    · rintro (rfl | ht)
      · exact le_rfl
      · exact ht.le
  rw [hset, continuousWithinAt_insert_self]
  change Tendsto (leftEndpointExtension α T a) (𝓝[<] T) (𝓝 (leftEndpointExtension α T a T))
  simp only [leftEndpointExtension, lt_self_iff_false, if_false]
  apply ha.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (if_pos ht).symm

theorem hasDerivWithinAt_leftEndpointExtension {T : ℝ} (hT : 0 < T)
    {α α' : ℝ → E} {a d : E}
    (hd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt α (α' t) t)
    (ha : Tendsto α (𝓝[<] T) (𝓝 a)) (hdlim : Tendsto α' (𝓝[<] T) (𝓝 d)) :
    HasDerivWithinAt (leftEndpointExtension α T a) d (Iic T) T := by
  have hde (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      HasDerivAt (leftEndpointExtension α T a) (α' t) t := by
    apply (hd t ht).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ht.2] with s hs
    exact if_pos hs
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun t ht => (hde t ht).differentiableAt.differentiableWithinAt)
    ((continuousWithinAt_leftEndpointExtension ha).mono (fun _ ht => ht.2.le))
    (Ioo_mem_nhdsLT hT)
  apply hdlim.congr'
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht
  exact (hde t ht).deriv.symm

end Euler2D

end
