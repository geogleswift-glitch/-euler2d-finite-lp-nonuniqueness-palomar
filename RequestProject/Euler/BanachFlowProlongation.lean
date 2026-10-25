module

public import RequestProject.Euler.BanachFlowDerivativeExistence

/-! Genuine first prolongation of a Banach vector field. Its true
operator component is identified with the initial-point derivative of
the original flow, giving a rigorous regularity-raising step. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def banachFlowProlongation (f : E → E) (p : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (f p.1, (fderiv ℝ f p.1).comp p.2)

theorem contDiffOn_banachFlowProlongation
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (banachFlowProlongation f) (U ×ˢ (univ : Set (E →L[ℝ] E))) := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hfst : ContDiffOn ℝ ∞ (fun p : E × (E →L[ℝ] E) => f p.1)
      (U ×ˢ (univ : Set (E →L[ℝ] E))) :=
    hf.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
  have hDf : ContDiffOn ℝ ∞ (fun p : E × (E →L[ℝ] E) => fderiv ℝ f p.1)
      (U ×ˢ (univ : Set (E →L[ℝ] E))) :=
    hD.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
  exact hfst.prodMk (hDf.clm_comp contDiff_snd.contDiffOn)

theorem banachFlowProlongation_first_eq
    {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U V T X) {K : ℝ≥0} (hLip : LipschitzOnWith K f U)
    {W V' : Set (E × (E →L[ℝ] E))} {Y : (E × (E →L[ℝ] E)) → ℝ → E × (E →L[ℝ] E)}
    (hY : IsBanachFlowOn (banachFlowProlongation f) W V' T Y)
    (hW : ∀ p ∈ W, p.1 ∈ U) {b : E} (hb : b ∈ V)
    (hb' : (b, ContinuousLinearMap.id ℝ E) ∈ V') :
    EqOn (fun u => (Y (b, ContinuousLinearMap.id ℝ E) u).1) (X b) (Icc (0 : ℝ) T) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ : ℝ => f) (s := fun _ : ℝ => U) (K := K) (fun _ _ => hLip)
    (hY.continuous _ hb').fst
    (fun u hu => ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt u
      (hY.hasDerivAt _ hb' u ⟨hu.1, hu.2.le⟩)).hasDerivWithinAt)
    (fun u hu => hW _ (hY.mem _ hb' u ⟨hu.1, hu.2.le⟩))
    (hX.continuous b hb)
    (fun u hu => (hX.hasDerivAt b hb u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => hX.mem b hb u ⟨hu.1, hu.2.le⟩)
  rw [hY.initial _ hb', hX.initial b hb]

/-- A genuinely existing prolonged trajectory supplies the actual
initial-point derivative, without assuming differentiability of either
flow in its initial point. -/
theorem hasFDerivAt_banachFlow_from_prolongation
    {f : E → E} {U V : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {T : ℝ} (hT : 0 ≤ T)
    {X : E → ℝ → E} (hX : IsBanachFlowOn f U V T X)
    {W V' : Set (E × (E →L[ℝ] E))} {Y : (E × (E →L[ℝ] E)) → ℝ → E × (E →L[ℝ] E)}
    (hY : IsBanachFlowOn (banachFlowProlongation f) W V' T Y)
    (hW : ∀ p ∈ W, p.1 ∈ U) {b : E} (hb : V ∈ 𝓝 b)
    (hb' : (b, ContinuousLinearMap.id ℝ E) ∈ V') {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt (fun a => X a t) (Y (b, ContinuousLinearMap.id ℝ E) t).2 b := by
  obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hb
  have hX' : IsBanachFlowOn f U (ball b ρ) T X :=
    ⟨fun a ha => hX.initial a (hρV ha), fun a ha => hX.continuous a (hρV ha),
      fun a ha => hX.hasDerivAt a (hρV ha), fun a ha => hX.mem a (hρV ha)⟩
  have heq := banachFlowProlongation_first_eq hX hLip hY hW (mem_of_mem_nhds hb) hb'
  have hAd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun s => (Y (b, ContinuousLinearMap.id ℝ E) s).2)
        ((fderiv ℝ f (X b u)).comp (Y (b, ContinuousLinearMap.id ℝ E) u).2) u := by
    have hd := (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt u
      (hY.hasDerivAt _ hb' u hu)
    simpa only [Function.comp_def, ContinuousLinearMap.coe_snd',
      banachFlowProlongation, heq hu] using hd
  exact hasFDerivAt_banachFlow_of_variational hU hf hLip hρ hT hX'
    (hY.continuous _ hb').snd (congrArg Prod.snd (hY.initial _ hb')) hAd ht

/-- The induction step for initial-data regularity: order `n` of the
actual prolonged flow implies order `n+1` of the original actual flow. -/
theorem contDiffOn_succ_banachFlow_from_prolongation
    {f : E → E} {U V : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {T : ℝ} (hT : 0 ≤ T)
    {X : E → ℝ → E} (hX : IsBanachFlowOn f U V T X)
    {W V' : Set (E × (E →L[ℝ] E))} {Y : (E × (E →L[ℝ] E)) → ℝ → E × (E →L[ℝ] E)}
    (hY : IsBanachFlowOn (banachFlowProlongation f) W V' T Y)
    (hW : ∀ p ∈ W, p.1 ∈ U) {O : Set E} (hO : IsOpen O) (hOV : O ⊆ V)
    (hOY : ∀ b ∈ O, (b, ContinuousLinearMap.id ℝ E) ∈ V')
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hYn : ContDiffOn ℝ n (fun p => Y p t) V') :
    ContDiffOn ℝ (n + 1 : ℕ) (fun b => X b t) O := by
  have hA : ContDiffOn ℝ n (fun b => (Y (b, ContinuousLinearMap.id ℝ E) t).2) O :=
    hYn.snd.comp (contDiff_id.prodMk contDiff_const).contDiffOn hOY
  rw [Nat.cast_add, Nat.cast_one]
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := (n : WithTop ℕ∞)) hO.uniqueDiffOn).mpr
  refine ⟨by simp, fun b => (Y (b, ContinuousLinearMap.id ℝ E) t).2, hA, ?_⟩
  intro b hb
  exact (hasFDerivAt_banachFlow_from_prolongation hU hf hLip hT hX hY hW
    (mem_of_superset (hO.mem_nhds hb) hOV) (hOY b hb) ht).hasFDerivWithinAt

end Euler2D

end
