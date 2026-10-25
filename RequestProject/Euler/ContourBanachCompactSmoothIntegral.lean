module

public import RequestProject.Euler.ContourWeightedCompactSmoothIntegral

/-! Compact-parameter integration on an arbitrary normed parameter
space. A genuine tube-neighborhood argument replaces compactness of
parameter balls, so the parameter may be an infinite-dimensional Banach
space. All hypotheses are local to the actual open parameter domain. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff

namespace Euler2D

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_local_uniform_bound_of_continuousOn_compact
    {S : Set ℝ} (hS : IsCompact S) {U : Set P} (hU : IsOpen U)
    (F : P → ℝ → E) (hF : ContinuousOn (Function.uncurry F) (U ×ˢ S))
    {p₀ : P} (hp₀ : p₀ ∈ U) :
    ∃ (C : ℝ) (B : Set P), IsOpen B ∧ p₀ ∈ B ∧ B ⊆ U ∧
      ∀ p ∈ B, ∀ u ∈ S, ‖F p u‖ ≤ C := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let Fs : U × S → E := fun q => F q.1 q.2
  have hc : Continuous Fs := by
    exact hF.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun q => ⟨q.1.property, q.2.property⟩)
  have hslice : Continuous (fun u : S => Fs (⟨p₀, hp₀⟩, u)) :=
    hc.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hslice.continuousOn
  have ho : IsOpen {q : U × S | ‖Fs q‖ < C + 1} := hc.norm.isOpen_preimage _ isOpen_Iio
  have hin : ({(⟨p₀, hp₀⟩ : U)} ×ˢ (univ : Set S)) ⊆ {q | ‖Fs q‖ < C + 1} := by
    intro q hq
    rcases hq with ⟨hq, _⟩
    rw [mem_singleton_iff] at hq
    change ‖Fs (q.1, q.2)‖ < C + 1
    rw [hq]
    exact (hC q.2 (mem_univ _)).trans_lt (lt_add_one C)
  obtain ⟨V, W, hV, _, hpV, hW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ ho hin
  refine ⟨C + 1, Subtype.val '' V, hU.isOpenMap_subtype_val V hV,
    ⟨⟨p₀, hp₀⟩, hpV (mem_singleton _), rfl⟩, ?_, ?_⟩
  · rintro p ⟨q, _, rfl⟩
    exact q.property
  · rintro p ⟨q, hq, rfl⟩ u hu
    exact (hVW (a := (q, (⟨u, hu⟩ : S))) ⟨hq, hW (mem_univ _)⟩).le

theorem hasFDerivAt_banachWeightedSetIntegral_of_continuousOn_compact
    {S : Set ℝ} (hS : IsCompact S) {w : ℝ → ℝ} (hw : IntegrableOn w S)
    {U : Set P} (hU : IsOpen U) (F : P → ℝ → E) (G : P → ℝ → P →L[ℝ] E)
    (hF : ContinuousOn (Function.uncurry F) (U ×ˢ S))
    (hG : ContinuousOn (Function.uncurry G) (U ×ˢ S))
    (hderiv : ∀ p ∈ U, ∀ u ∈ S, HasFDerivAt (fun q => F q u) (G p u) p)
    {p₀ : P} (hp₀ : p₀ ∈ U) :
    HasFDerivAt (fun p => ∫ u in S, w u • F p u) (∫ u in S, w u • G p₀ u) p₀ := by
  have hFc (p : P) (hp : p ∈ U) : ContinuousOn (F p) S :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨hp, hu⟩)
  have hGc (p : P) (hp : p ∈ U) : ContinuousOn (G p) S :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨hp, hu⟩)
  obtain ⟨C, B, hB, hpB, hBU, hbound⟩ :=
    exists_local_uniform_bound_of_continuousOn_compact hS hU G hG hp₀
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p u => w u • F p u) (F' := fun p u => w u • G p u)
    (μ := volume.restrict S) (s := B) (bound := fun u => C * ‖w u‖)
    (hB.mem_nhds hpB)
    (by
      filter_upwards [hU.mem_nhds hp₀] with p hp
      exact hw.aestronglyMeasurable.smul ((hFc p hp).aestronglyMeasurable hS.measurableSet))
    (integrableOn_smul_continuousOn_compact hS hw (hFc p₀ hp₀))
    (hw.aestronglyMeasurable.smul ((hGc p₀ hp₀).aestronglyMeasurable hS.measurableSet))
  · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
    intro p hp
    rw [norm_smul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound p hp u hu) (norm_nonneg _)
  · exact hw.norm.const_mul C
  · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
    intro p hp
    exact (hderiv p (hBU hp) u hu).const_smul (w u)

theorem contDiffOn_nat_banachWeightedSetIntegral_of_compact
    {S : Set ℝ} (hS : IsCompact S) {w : ℝ → ℝ} (hw : IntegrableOn w S)
    {U : Set P} (hU : IsOpen U) (n : ℕ) (F : P → ℝ → E)
    (hF : ∀ q : P × ℝ, q ∈ U ×ˢ S → ContDiffAt ℝ n (Function.uncurry F) q) :
    ContDiffOn ℝ n (fun p => ∫ u in S, w u • F p u) U := by
  induction n generalizing E with
  | zero =>
    simp only [Nat.cast_zero] at hF ⊢
    rw [contDiffOn_zero]
    have hc : ContinuousOn (Function.uncurry F) (U ×ˢ S) :=
      fun q hq => (hF q hq).continuousAt.continuousWithinAt
    intro p₀ hp₀
    apply ContinuousAt.continuousWithinAt
    obtain ⟨C, B, hB, hpB, _, hbound⟩ :=
      exists_local_uniform_bound_of_continuousOn_compact hS hU F hc hp₀
    apply continuousAt_of_dominated (F := fun p u => w u • F p u) (x₀ := p₀)
      (bound := fun u => C * ‖w u‖) (μ := volume.restrict S)
    · filter_upwards [hU.mem_nhds hp₀] with p hp
      exact hw.aestronglyMeasurable.smul
        ((hc.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun _ hu => ⟨hp, hu⟩)).aestronglyMeasurable hS.measurableSet)
    · filter_upwards [hB.mem_nhds hpB] with p hp
      filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      rw [norm_smul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hbound p hp u hu) (norm_nonneg _)
    · exact hw.norm.const_mul C
    · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      have hin : ContinuousAt (fun p : P => (p, u)) p₀ :=
        continuousAt_id.prodMk continuousAt_const
      exact ((hF (p₀, u) ⟨hp₀, hu⟩).continuousAt.comp
        (f := fun p : P => (p, u)) (x := p₀) hin).const_smul (w u)
  | succ n ih =>
    let G : P → ℝ → P →L[ℝ] E := fun p u =>
      (fderiv ℝ (Function.uncurry F) (p, u)).comp (ContinuousLinearMap.inl ℝ P ℝ)
    have hG (q : P × ℝ) (hq : q ∈ U ×ˢ S) :
        ContDiffAt ℝ n (Function.uncurry G) q := by
      exact ((hF q hq).fderiv_right (by norm_cast)).clm_comp contDiffAt_const
    have hderiv (p : P) (hp : p ∈ U) (u : ℝ) (hu : u ∈ S) :
        HasFDerivAt (fun q => F q u) (G p u) p := by
      have hd := ((hF (p, u) ⟨hp, hu⟩).differentiableAt (by simp)).hasFDerivAt
      have hin : HasFDerivAt (fun q : P => (q, u)) (ContinuousLinearMap.inl ℝ P ℝ) p :=
        (hasFDerivAt_id p).prodMk (hasFDerivAt_const u p)
      exact hd.comp p hin
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (n := (n : WithTop ℕ∞)) hU.uniqueDiffOn).mpr
    refine ⟨by simp, fun p => ∫ u in S, w u • G p u, ih G hG, ?_⟩
    intro p hp
    exact (hasFDerivAt_banachWeightedSetIntegral_of_continuousOn_compact hS hw hU F G
      (fun q hq => (hF q hq).continuousAt.continuousWithinAt)
      (fun q hq => (hG q hq).continuousAt.continuousWithinAt) hderiv hp).hasFDerivWithinAt

theorem contDiffOn_banachWeightedSetIntegral_of_compact
    {S : Set ℝ} (hS : IsCompact S) {w : ℝ → ℝ} (hw : IntegrableOn w S)
    {U : Set P} (hU : IsOpen U) (F : P → ℝ → E)
    (hF : ∀ q : P × ℝ, q ∈ U ×ˢ S → ContDiffAt ℝ ∞ (Function.uncurry F) q) :
    ContDiffOn ℝ ∞ (fun p => ∫ u in S, w u • F p u) U := by
  apply contDiffOn_infty.mpr
  intro n
  exact contDiffOn_nat_banachWeightedSetIntegral_of_compact hS hw hU n F
    (fun q hq => (hF q hq).of_le (WithTop.coe_le_coe.mpr le_top))

theorem contDiffOn_banachSetIntegral_of_compact
    {S : Set ℝ} (hS : IsCompact S) {U : Set P} (hU : IsOpen U) (F : P → ℝ → E)
    (hF : ∀ q : P × ℝ, q ∈ U ×ˢ S → ContDiffAt ℝ ∞ (Function.uncurry F) q) :
    ContDiffOn ℝ ∞ (fun p => ∫ u in S, F p u) U := by
  simpa only [one_smul] using
    (contDiffOn_banachWeightedSetIntegral_of_compact hS
      (w := fun _ : ℝ => 1) (integrableOn_const hS.measure_ne_top) hU F hF)

end Euler2D

end
