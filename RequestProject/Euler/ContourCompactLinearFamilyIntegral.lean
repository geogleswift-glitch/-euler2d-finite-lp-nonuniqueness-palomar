module

public import RequestProject.Euler.ContourBanachCompactSmoothIntegral

/-! Smooth dependence of a genuine compact-parameter integral whose
linear parameter family is only continuous in the integration variable.
No derivatives in the integration variable are required. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace Euler2D

variable {P V E₀ E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def compactLinearFamilyDerivativeCoefficient (L : P →L[ℝ] V) (T : E₀ →L[ℝ] E) :
    (V →L[ℝ] E₀) →L[ℝ] P →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ P E₀ E) T).comp
    ((ContinuousLinearMap.compL ℝ P V E₀).flip L)

theorem continuousOn_compactLinearFamilyDerivativeCoefficient
    {S : Set ℝ} {L : ℝ → P →L[ℝ] V} {T : ℝ → E₀ →L[ℝ] E}
    (hL : ContinuousOn L S) (hT : ContinuousOn T S) :
    ContinuousOn (fun u => compactLinearFamilyDerivativeCoefficient (L u) (T u)) S := by
  exact ((ContinuousLinearMap.compL ℝ P E₀ E).continuous.comp_continuousOn hT).clm_comp
    ((ContinuousLinearMap.compL ℝ P V E₀).flip.continuous.comp_continuousOn hL)

theorem continuousOn_compactLinearFamily_composition
    {S : Set ℝ} {U : Set P} {W : Set V}
    (L : ℝ → P →L[ℝ] V) (T : ℝ → E₀ →L[ℝ] E) (φ : V → E₀)
    (hL : ContinuousOn L S) (hT : ContinuousOn T S) (hφ : ContinuousOn φ W)
    (himage : ∀ p ∈ U, ∀ u ∈ S, L u p ∈ W) :
    ContinuousOn (Function.uncurry (fun p u => T u (φ (L u p)))) (U ×ˢ S) := by
  have hs : ContinuousOn (fun q : P × ℝ => q.2) (U ×ˢ S) := continuous_snd.continuousOn
  have hp : ContinuousOn (fun q : P × ℝ => q.1) (U ×ˢ S) := continuous_fst.continuousOn
  have hLs : ContinuousOn (fun q : P × ℝ => L q.2) (U ×ˢ S) :=
    hL.comp hs (fun _ hq => hq.2)
  have hTs : ContinuousOn (fun q : P × ℝ => T q.2) (U ×ˢ S) :=
    hT.comp hs (fun _ hq => hq.2)
  have hi := hLs.clm_apply hp
  exact hTs.clm_apply (hφ.comp hi (fun q hq => himage q.1 hq.1 q.2 hq.2))

theorem contDiffOn_nat_weightedIntegral_compactLinearFamily
    {S : Set ℝ} (hS : IsCompact S) {w : ℝ → ℝ} (hw : IntegrableOn w S)
    {U : Set P} (hU : IsOpen U) {W : Set V} (hW : IsOpen W) (n : ℕ)
    (L : ℝ → P →L[ℝ] V) (T : ℝ → E₀ →L[ℝ] E) (φ : V → E₀)
    (hL : ContinuousOn L S) (hT : ContinuousOn T S) (hφ : ContDiffOn ℝ n φ W)
    (himage : ∀ p ∈ U, ∀ u ∈ S, L u p ∈ W) :
    ContDiffOn ℝ n (fun p => ∫ u in S, w u • T u (φ (L u p))) U := by
  induction n generalizing E₀ E with
  | zero =>
    simp only [Nat.cast_zero] at hφ ⊢
    rw [contDiffOn_zero] at hφ ⊢
    have hc := continuousOn_compactLinearFamily_composition L T φ hL hT hφ himage
    intro p₀ hp₀
    apply ContinuousAt.continuousWithinAt
    obtain ⟨C, B, hB, hpB, _, hbound⟩ :=
      exists_local_uniform_bound_of_continuousOn_compact hS hU _ hc hp₀
    apply continuousAt_of_dominated (F := fun p u => w u • T u (φ (L u p)))
      (x₀ := p₀) (bound := fun u => C * ‖w u‖) (μ := volume.restrict S)
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
      have hLup : ContinuousAt (fun p : P => L u p) p₀ := (L u).continuous.continuousAt
      have hφat : ContinuousAt φ (L u p₀) :=
        (hφ (L u p₀) (himage p₀ hp₀ u hu)).continuousAt
          (hW.mem_nhds (himage p₀ hp₀ u hu))
      exact (((T u).continuous.continuousAt.comp (hφat.comp hLup)).const_smul (w u))
  | succ n ih =>
    let T' : ℝ → (V →L[ℝ] E₀) →L[ℝ] P →L[ℝ] E :=
      fun u => compactLinearFamilyDerivativeCoefficient (L u) (T u)
    have hT' : ContinuousOn T' S :=
      continuousOn_compactLinearFamilyDerivativeCoefficient hL hT
    have hφ' : ContDiffOn ℝ n (fderiv ℝ φ) W :=
      hφ.fderiv_of_isOpen hW (by norm_cast)
    have hc := continuousOn_compactLinearFamily_composition L T φ hL hT hφ.continuousOn himage
    have hc' := continuousOn_compactLinearFamily_composition L T' (fderiv ℝ φ)
      hL hT' hφ'.continuousOn himage
    have hderiv (p : P) (hp : p ∈ U) (u : ℝ) (hu : u ∈ S) :
        HasFDerivAt (fun q => T u (φ (L u q))) (T' u (fderiv ℝ φ (L u p))) p := by
      have hφat : ContDiffAt ℝ (n + 1 : ℕ) φ (L u p) :=
        (hφ (L u p) (himage p hp u hu)).contDiffAt (hW.mem_nhds (himage p hp u hu))
      have hd := (hφat.differentiableAt (by simp)).hasFDerivAt
      exact (T u).hasFDerivAt.comp p (hd.comp p (L u).hasFDerivAt)
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (n := (n : WithTop ℕ∞)) hU.uniqueDiffOn).mpr
    refine ⟨by simp, fun p => ∫ u in S, w u • T' u (fderiv ℝ φ (L u p)),
      ih T' (fderiv ℝ φ) hT' hφ', ?_⟩
    intro p hp
    exact (hasFDerivAt_banachWeightedSetIntegral_of_continuousOn_compact hS hw hU
      (fun p u => T u (φ (L u p))) (fun p u => T' u (fderiv ℝ φ (L u p)))
      hc hc' hderiv hp).hasFDerivWithinAt

theorem contDiffOn_weightedIntegral_compactLinearFamily
    {S : Set ℝ} (hS : IsCompact S) {w : ℝ → ℝ} (hw : IntegrableOn w S)
    {U : Set P} (hU : IsOpen U) {W : Set V} (hW : IsOpen W)
    (L : ℝ → P →L[ℝ] V) (T : ℝ → E₀ →L[ℝ] E) (φ : V → E₀)
    (hL : ContinuousOn L S) (hT : ContinuousOn T S) (hφ : ContDiffOn ℝ ∞ φ W)
    (himage : ∀ p ∈ U, ∀ u ∈ S, L u p ∈ W) :
    ContDiffOn ℝ ∞ (fun p => ∫ u in S, w u • T u (φ (L u p))) U := by
  apply contDiffOn_infty.mpr
  intro n
  exact contDiffOn_nat_weightedIntegral_compactLinearFamily hS hw hU hW n L T φ hL hT
    (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) himage

end Euler2D

end
