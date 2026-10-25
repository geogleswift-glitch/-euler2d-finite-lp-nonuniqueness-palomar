module

public import Mathlib

/-!
# Compactness from spatial approximations

The functional-analytic part of Lemma `cp:lem:compactness`: uniformly
Lipschitz paths whose values have compact closure admit a uniformly
convergent subsequence. Compact spatial approximations imply the required
total boundedness. No Euler existence or Fourier estimate is assumed proved.
-/

@[expose] public section

open Set Metric Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

/-- Uniform approximation by compact sets gives total boundedness. -/
theorem totallyBounded_of_compact_approx {E : Type*} [PseudoMetricSpace E]
    {s : Set E}
    (happrox : ∀ ε > (0 : ℝ), ∃ K : Set E, IsCompact K ∧
      ∀ x ∈ s, ∃ y ∈ K, dist x y < ε) : TotallyBounded s := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨K, hK, hnear⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨a, ha, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (ε / 2) (half_pos hε)
  refine ⟨a, ha, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hnear x hx
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy)
  apply mem_iUnion₂.mpr
  refine ⟨z, hz, ?_⟩
  change dist x z < ε
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy hyz
    _ = ε := add_halves ε

/-- Finite-rank continuous linear approximations make a bounded set totally
bounded when their errors vanish uniformly on that set. -/
theorem totallyBounded_of_finiteRank_approx
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set E} (hs : Bornology.IsBounded s)
    (Q : ℕ → E →L[𝕜] E)
    (hfinite : ∀ m, FiniteDimensional 𝕜 (LinearMap.range (Q m).toLinearMap))
    (happrox : ∀ ε > (0 : ℝ), ∃ m, ∀ x ∈ s, ‖x - Q m x‖ < ε) :
    TotallyBounded s := by
  obtain ⟨R, hR⟩ := hs.exists_norm_le
  apply totallyBounded_of_compact_approx
  intro ε hε
  obtain ⟨m, hm⟩ := happrox ε hε
  let P := LinearMap.range (Q m).toLinearMap
  letI : FiniteDimensional 𝕜 P := hfinite m
  letI : ProperSpace P := FiniteDimensional.proper 𝕜 P
  refine ⟨(fun y : P => (y : E)) '' closedBall 0 (‖Q m‖ * R),
    (isCompact_closedBall (0 : P) (‖Q m‖ * R)).image continuous_subtype_val, ?_⟩
  intro x hx
  refine ⟨Q m x, ?_, ?_⟩
  · refine ⟨⟨Q m x, ⟨x, rfl⟩⟩, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, ← Submodule.norm_coe]
    exact (Q m).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))
  · simpa only [dist_eq_norm] using hm x hx

/-- Arzelà--Ascoli in the form needed by the finite Euler approximants. -/
theorem uniform_subseq_of_totallyBounded
    {A E : Type*} [PseudoMetricSpace A] [CompactSpace A]
    [MetricSpace E] [CompleteSpace E]
    (U : ℕ → A → E) (L : ℝ≥0) (hlip : ∀ n, LipschitzWith L (U n))
    {s : Set E} (hs : TotallyBounded s) (hvalues : ∀ n t, U n t ∈ s) :
    ∃ u : A → E, Continuous u ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly (fun n => U (φ n)) u atTop := by
  let F : ℕ → A →ᵇ E := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨U n, (hlip n).continuous⟩
  have heq : Equicontinuous ((↑) : range F → A → E) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r => (L : ℝ) * r)
      (by simpa using tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)))
    intro x y f
    obtain ⟨n, hn⟩ := f.property
    simpa only [← hn, F, BoundedContinuousFunction.mkOfCompact_apply,
      ContinuousMap.coe_mk] using (hlip n).dist_le_mul x y
  have hcompact : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli (closure s)
      (hs.closure.isCompact_of_isClosed isClosed_closure)
      (range F) (fun f t hf => by
        obtain ⟨n, rfl⟩ := hf
        exact subset_closure (hvalues n t)) heq
  obtain ⟨f, _, φ, hφ, hlim⟩ := hcompact.isSeqCompact
    (fun n => subset_closure (mem_range_self n))
  refine ⟨f, f.continuous, φ, hφ, ?_⟩
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim

/-- Compactness from uniform finite-rank truncation errors and a common
Lipschitz constant, in the form used by the finite Euler solutions. -/
theorem compactness_by_truncation
    {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
    [PseudoMetricSpace A] [CompactSpace A]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (U : ℕ → A → E) (L : ℝ≥0) (hlip : ∀ n, LipschitzWith L (U n))
    (M : ℝ) (hbound : ∀ n t, ‖U n t‖ ≤ M)
    (Q : ℕ → E →L[𝕜] E)
    (hfinite : ∀ m, FiniteDimensional 𝕜 (LinearMap.range (Q m).toLinearMap))
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (happrox : ∀ m n t, ‖U n t - Q m (U n t)‖ ≤ err m) :
    ∃ u : A → E, Continuous u ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly (fun n => U (φ n)) u atTop := by
  let s : Set E := range (fun p : ℕ × A => U p.1 p.2)
  have hsbound : Bornology.IsBounded s := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro x ⟨⟨n, t⟩, rfl⟩
    exact hbound n t
  have hstb : TotallyBounded s := by
    apply totallyBounded_of_finiteRank_approx hsbound Q hfinite
    intro ε hε
    obtain ⟨m, hm⟩ := (herr.eventually (gt_mem_nhds hε)).exists
    refine ⟨m, ?_⟩
    rintro x ⟨⟨n, t⟩, rfl⟩
    exact (happrox m n t).trans_lt hm
  exact uniform_subseq_of_totallyBounded U L hlip hstb
    (fun n t => mem_range_self (n, t))

end Euler2D

end
