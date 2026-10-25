module

public import RequestProject.Euler.WeakTestSeparation
public import RequestProject.Euler.CompactTestTopology
public import RequestProject.Euler.CurlCompactnessLimit
public import RequestProject.Euler.VelocityCurlBound

/-!
# Strong time compactness from the weak Euler equation and a curl bound

Fourier compactness supplies a compact state set. On that set the
smooth solenoidal pairings determine the strong topology. Their uniform
time modulus follows from the actual weak Euler equation and the energy
bound, so no separate time Lipschitz assumption is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Euler2D

theorem uniform_subseq_of_weakEuler_curl_bounds
    {T : ℝ} (hT : 0 < T) {U : ℕ → ℝ → L2T} {u₀ : ℕ → L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀ n) (U n))
    {M : ℝ} (hbound : ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤ M)
    {q : ENNReal} (hq : 2 ≤ q) {C : ℝ}
    (hcurl : ∀ n, CurlBoundedBy T q C (U n)) :
    ∃ u : ℝ → L2T, ContinuousOn u (Icc 0 T) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformlyOn (fun n => U (φ n)) u atTop (Icc 0 T) := by
  let V : ℕ → Icc (0 : ℝ) T → L2T := fun n t => U n t
  let s : Set L2T := range (fun p : ℕ × Icc (0 : ℝ) T => V p.1 p.2)
  have hsbound : Bornology.IsBounded s := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro u ⟨⟨n, t⟩, rfl⟩
    exact hbound n t t.property
  have hstb : TotallyBounded s := by
    apply totallyBounded_of_curl_Lq_bound hsbound hq
    rintro u ⟨⟨n, t⟩, rfl⟩
    exact ⟨(hU n).divFree t t.property, hcurl n t t.property⟩
  have hK : IsCompact (closure s) := hstb.closure.isCompact_of_isClosed isClosed_closure
  have hdivs : s ⊆ {u : L2T | DivFree u} := by
    rintro u ⟨⟨n, t⟩, rfl⟩
    exact (hU n).divFree t t.property
  have hdivK : closure s ⊆ {u : L2T | DivFree u} :=
    closure_minimal hdivs isClosed_setOf_divFree
  have hinj : Set.InjOn weakTestMap (closure s) := fun u hu v hv heq =>
    eq_of_smooth_divFree_pairings (hdivK hu) (hdivK hv) heq
  have htests : ∀ ψ : SmoothDivFreeTest,
      Equicontinuous (fun n t => weakTestMap (V n t) ψ) := by
    intro ψ
    obtain ⟨L, hL⟩ := uniform_lipschitz_spatial_test_pairings hT hU hbound
      ψ.2.1 ψ.2.2.1 ψ.2.2.2
    apply Metric.equicontinuous_of_continuity_modulus (fun r => (L : ℝ) * r)
      (by
        simpa using tendsto_const_nhds.mul
          (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)))
    intro t r n
    exact (hL n).dist_le_mul t r
  obtain ⟨v, _, _, φ, hφ, hv⟩ := uniform_subseq_of_compact_tests hK weakTestMap
    continuous_weakTestMap.continuousOn hinj V
    (fun n t => subset_closure (mem_range_self (n, t))) htests
  let u : ℝ → L2T := fun t => if ht : t ∈ Icc 0 T then v ⟨t, ht⟩ else 0
  have hlim : TendstoUniformlyOn (fun n => U (φ n)) u atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hv ε hε] with n hn t ht
    simpa only [u, V, dif_pos ht] using hn ⟨t, ht⟩
  exact ⟨u, hlim.continuousOn (Eventually.of_forall fun n => (hU (φ n)).continuous).frequently,
    φ, hφ, hlim⟩

/-- Initial convergence and common vorticity bounds suffice. The
velocity bound is derived from the curl and conserved spatial mean. -/
theorem uniform_subseq_of_weakEuler_curl_and_initial_convergence
    {T : ℝ} (hT : 0 < T) {U : ℕ → ℝ → L2T} {u₀ : ℕ → L2T} {datum : L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀ n) (U n))
    (hinit : Tendsto u₀ atTop (𝓝 datum))
    {q : ENNReal} (hq : 2 ≤ q) {C : ℝ}
    (hcurl : ∀ n, CurlBoundedBy T q C (U n)) :
    ∃ u : ℝ → L2T, ContinuousOn u (Icc 0 T) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformlyOn (fun n => U (φ n)) u atTop (Icc 0 T) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto u₀ hinit).exists_norm_le
  exact uniform_subseq_of_weakEuler_curl_bounds hT hU
    (uniform_velocity_bound_of_curl_and_initial hT hU (fun n => hB _ (mem_range_self n)) hq hcurl)
      hq hcurl

/-- All compactness and departure conclusions follow from genuine weak
Euler solutions with common velocity and vorticity bounds. -/
theorem weak_limit_with_departure_of_uniform_curl
    {T a b c : ℝ} (hT : 0 < T) (ha : 0 < a) (hb : b < T) (hc : 0 < c)
    {U : ℕ → ℝ → L2T} {u₀n : ℕ → L2T} {u₀ : L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀n n) (U n))
    (hinit : Tendsto u₀n atTop (𝓝 u₀))
    {M : ℝ} (hbound : ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤ M)
    {q : ENNReal} (hq : 2 ≤ q) {C : ℝ}
    (hcurl : ∀ n, CurlBoundedBy T q C (U n))
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc a b)
    (hdep : ∀ n, c ≤ ‖U n (τ n) - u₀‖) :
    ∃ u : ℝ → L2T, IsWeakEulerSolution T u₀ u ∧ CurlBoundedBy T q C u ∧
      ∃ t ∈ Ioo 0 T, c ≤ ‖u t - u₀‖ ∧ u t ≠ u₀ := by
  obtain ⟨u, hu, φ, hφ, hlim⟩ := uniform_subseq_of_weakEuler_curl_bounds hT hU hbound hq hcurl
  have hweak : IsWeakEulerSolution T u₀ u :=
    isWeakEulerSolution_of_tendstoUniformlyOn hT.le (fun n => hU (φ n))
      hlim (hinit.comp hφ.tendsto_atTop)
  have hcU : CurlBoundedBy T q C u := curlBoundedBy_of_tendsto hq
    (fun n => hcurl (φ n)) (fun t ht => hlim.tendsto_at ht)
  obtain ⟨t, ht, hct⟩ := exists_departure_lowerBound_of_tendstoUniformlyOn
    ha.le hb.le hu hlim (tendsto_const_nhds (x := u₀))
    (fun n => hτ (φ n)) (fun n => hdep (φ n))
  exact ⟨u, hweak, hcU, t, ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩, hct,
    sub_ne_zero.mp (norm_pos_iff.mp (hc.trans_le hct))⟩

end Euler2D

end
