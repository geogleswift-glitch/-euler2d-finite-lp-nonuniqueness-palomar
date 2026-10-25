module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! A genuine local variational solution in the operator Banach space.
Picard--Lindelöf is applied directly on a bounded operator ball; no
finite-dimensional cutoff or unproved linear ODE solution is used. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

def banachFlowVariationalTime (K : ℝ≥0) : ℝ := (1 / (4 * ((K : ℝ) + 1))) / 2

theorem banachFlowVariationalTime_pos (K : ℝ≥0) : 0 < banachFlowVariationalTime K := by
  unfold banachFlowVariationalTime
  positivity

theorem exists_banachFlow_variational_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {B : ℝ → E →L[ℝ] E} {K : ℝ≥0} (hBc : Continuous B) (hB : ∀ t, ‖B t‖ ≤ K) :
    ∃ A : ℝ → E →L[ℝ] E, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc (-banachFlowVariationalTime K) (banachFlowVariationalTime K),
        HasDerivAt A ((B t).comp (A t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) (banachFlowVariationalTime K), ‖A t‖ ≤ Real.exp ((K : ℝ) * t) := by
  let τ : ℝ := 1 / (4 * ((K : ℝ) + 1))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  let f : ℝ → (E →L[ℝ] E) → E →L[ℝ] E := fun t A => (B t).comp A
  have hfL (t : ℝ) : LipschitzWith K (f t) := by
    apply LipschitzWith.of_dist_le_mul
    intro A C
    rw [dist_eq_norm]
    change ‖(B t).comp A - (B t).comp C‖ ≤ (K : ℝ) * dist A C
    rw [← ContinuousLinearMap.comp_sub, dist_eq_norm]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _))
  have hfM (t : ℝ) (A : E →L[ℝ] E)
      (hA : A ∈ closedBall (ContinuousLinearMap.id ℝ E) 1) : ‖f t A‖ ≤ (2 * K : ℝ≥0) := by
    have hAn : ‖A‖ ≤ 2 := by
      have hn := (norm_le_norm_sub_add A (ContinuousLinearMap.id ℝ E)).trans
        (add_le_add (mem_closedBall_iff_norm.mp hA) ContinuousLinearMap.norm_id_le)
      norm_num only at hn
      exact hn
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hB t) hAn (norm_nonneg A) K.coe_nonneg).trans_eq (by norm_cast; ring))
  let t₀ : Icc (-τ) τ := ⟨0, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof f t₀ (ContinuousLinearMap.id ℝ E) 1 0 (2 * K) K := by
    refine ⟨fun t _ => (hfL t).lipschitzOnWith, ?_, fun t _ A hA => hfM t A hA, ?_⟩
    · intro A _
      exact (hBc.clm_comp continuous_const).continuousOn
    · change (2 * (K : ℝ)) * max (τ - 0) (0 - -τ) ≤ 1 - 0
      simp only [sub_zero, zero_sub, neg_neg, max_self]
      dsimp only [τ]
      rw [← mul_div_assoc, mul_one, div_le_iff₀ (show 0 < 4 * ((K : ℝ) + 1) by positivity)]
      nlinarith [K.coe_nonneg]
  obtain ⟨A, hA0, hAd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let β : ℝ → E →L[ℝ] E := fun t => A (Set.projIcc (-τ) τ (by linarith) t)
  have hβ (t : ℝ) (ht : t ∈ Icc (-τ) τ) : β t = A t := by
    dsimp only [β]
    rw [Set.projIcc_of_mem _ ht]
  have hβc : Continuous β :=
    (HasDerivWithinAt.continuousOn hAd).restrict.comp (continuous_projIcc (h := by linarith))
  have hβ0 : β 0 = ContinuousLinearMap.id ℝ E := by
    rw [hβ 0 (by constructor <;> linarith)]
    exact hA0
  have hβd (t : ℝ) (ht : t ∈ Icc (-banachFlowVariationalTime K) (banachFlowVariationalTime K)) :
      HasDerivAt β ((B t).comp (β t)) t := by
    have hti : t ∈ Ioo (-τ) τ := by
      change -(τ / 2) ≤ t ∧ t ≤ τ / 2 at ht
      constructor <;> linarith [ht.1, ht.2]
    have hn : Icc (-τ) τ ∈ 𝓝 t := Icc_mem_nhds hti.1 hti.2
    have he : β =ᶠ[𝓝 t] A := by
      filter_upwards [hn] with s hs
      exact hβ s hs
    have hd := (hAd t ⟨hti.1.le, hti.2.le⟩).hasDerivAt hn
    simpa only [f, hβ t ⟨hti.1.le, hti.2.le⟩] using hd.congr_of_eventuallyEq he
  refine ⟨β, hβc, hβ0, hβd, ?_⟩
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hβc.continuousOn
    (fun u hu => (hβd u (by constructor <;>
      linarith [hu.1, hu.2, ht.2, banachFlowVariationalTime_pos K])).hasDerivWithinAt)
    (a := (0 : ℝ)) (b := t) (δ := 1) (ε := 0) (K := (K : ℝ))
    (by rw [hβ0]; exact ContinuousLinearMap.norm_id_le)
    (fun u hu => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [add_zero] using mul_le_mul_of_nonneg_right (hB u) (norm_nonneg (β u))))
    t ⟨ht.1, le_rfl⟩
  simpa only [gronwallBound_ε0, one_mul, sub_zero] using hg

end Euler2D

end
