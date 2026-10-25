module

public import RequestProject.Euler.BanachFlowVariational
public import Mathlib.Topology.Piecewise

/-! Finite-time fundamental operator curves in an arbitrary real Banach space.
The local linear solutions are concatenated with their endpoint values; the
derivatives agree at every joining time. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem hasDerivAt_banachVariational_glue
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {v : F} {c : ℝ}
    (hf : HasDerivAt f v c) (hg : HasDerivAt g v c) (he : f c = g c) :
    HasDerivAt (fun t => if t ≤ c then f t else g t) v c := by
  have hleft : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) v (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      exact if_pos ht
    · exact if_pos le_rfl
  have hright : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) v (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases htc : t ≤ c
      · have htc' : t = c := le_antisymm htc ht
        subst t
        simpa only [if_pos le_rfl] using he
      · exact if_neg htc
    · simpa only [if_pos le_rfl] using he
  have h := hleft.union hright
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using h

theorem exists_banachFlow_variational_curve_nat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {B : ℝ → E →L[ℝ] E} {K : ℝ≥0} (hBc : Continuous B) (hB : ∀ t, ‖B t‖ ≤ K)
    (n : ℕ) :
    ∃ A : ℝ → E →L[ℝ] E, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) * banachFlowVariationalTime K),
        HasDerivAt A ((B t).comp (A t)) t := by
  classical
  let δ := banachFlowVariationalTime K
  have hδ : 0 < δ := banachFlowVariationalTime_pos K
  induction n with
  | zero =>
      obtain ⟨A, hAc, hA0, hAd, _⟩ := exists_banachFlow_variational_curve hBc hB
      refine ⟨A, hAc, hA0, ?_⟩
      intro t ht
      have ht0 : t = 0 := by
        simp only [Nat.cast_zero, zero_mul, mem_Icc] at ht
        exact le_antisymm ht.2 ht.1
      subst t
      exact hAd 0 (by constructor <;> linarith)
  | succ n ih =>
      obtain ⟨A, hAc, hA0, hAd⟩ := ih
      let c : ℝ := (n : ℝ) * δ
      have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg n) hδ.le
      obtain ⟨C, hCc, hC0, hCd, _⟩ :=
        exists_banachFlow_variational_curve
          (hBc.comp (continuous_id.add continuous_const) : Continuous (fun t => B (t + c)))
          (fun t => hB (t + c))
      let G : ℝ → E →L[ℝ] E := fun t => (C (t - c)).comp (A c)
      have hGc : Continuous G :=
        (hCc.comp (continuous_id.sub continuous_const)).clm_comp continuous_const
      have hGc0 : G c = A c := by simp only [G, sub_self, hC0, ContinuousLinearMap.id_comp]
      have hGd (t : ℝ) (ht : t - c ∈ Icc (-δ) δ) :
          HasDerivAt G ((B t).comp (G t)) t := by
        have hd := (hCd (t - c) ht).scomp t ((hasDerivAt_id t).sub_const c)
        have hd' := hd.clm_comp (hasDerivAt_const t (A c))
        simpa only [G, Function.comp_apply, sub_add_cancel, one_smul, ContinuousLinearMap.comp_zero,
          add_zero, ContinuousLinearMap.comp_assoc, id_eq] using hd'
      let H : ℝ → E →L[ℝ] E := fun t => if t ≤ c then A t else G t
      have hHc : Continuous H := by
        apply hAc.if _ hGc
        intro t ht
        change t ∈ frontier (Iic c) at ht
        have ht' : t = c := by simpa only [frontier_Iic, mem_singleton_iff] using ht
        subst t
        exact hGc0.symm
      have hH0 : H 0 = ContinuousLinearMap.id ℝ E := by
        simpa only [H, if_pos hc] using hA0
      refine ⟨H, hHc, hH0, ?_⟩
      intro t ht
      have hbound : t ≤ c + δ := by
        have ht' := ht.2
        change t ≤ ((n + 1 : ℕ) : ℝ) * δ at ht'
        push_cast at ht'
        dsimp only [c]
        nlinarith [ht']
      rcases lt_trichotomy t c with htc | rfl | hct
      · have he : H =ᶠ[𝓝 t] A := by
          filter_upwards [Iio_mem_nhds htc] with s hs
          exact if_pos hs.le
        have hd := hAd t ⟨ht.1, htc.le⟩
        rw [show H t = A t from if_pos htc.le]
        exact hd.congr_of_eventuallyEq he
      · have hdA := hAd c ⟨hc, le_rfl⟩
        have hdG := hGd c (by simp only [sub_self, mem_Icc]; constructor <;> linarith)
        rw [hGc0] at hdG
        have hd := hasDerivAt_banachVariational_glue hdA hdG hGc0.symm
        simpa only [H, if_pos le_rfl] using hd
      · have he : H =ᶠ[𝓝 t] G := by
          filter_upwards [Ioi_mem_nhds hct] with s hs
          exact if_neg (not_le.mpr hs)
        have hd := hGd t (by constructor <;> linarith)
        rw [show H t = G t from if_neg (not_le.mpr hct)]
        exact hd.congr_of_eventuallyEq he

theorem exists_banachFlow_global_variational_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {B : ℝ → E →L[ℝ] E} {K : ℝ≥0} (hBc : Continuous B) (hB : ∀ t, ‖B t‖ ≤ K)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ A : ℝ → E →L[ℝ] E, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A ((B t).comp (A t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ‖A t‖ ≤ Real.exp ((K : ℝ) * t) := by
  have hδ := banachFlowVariationalTime_pos K
  obtain ⟨n, hn⟩ := exists_nat_gt (T / banachFlowVariationalTime K)
  have hTn : T ≤ (n : ℝ) * banachFlowVariationalTime K :=
    (div_lt_iff₀ hδ).mp hn |>.le
  obtain ⟨A, hAc, hA0, hAd⟩ := exists_banachFlow_variational_curve_nat hBc hB n
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt A ((B t).comp (A t)) t := hAd t ⟨ht.1, ht.2.trans hTn⟩
  refine ⟨A, hAc, hA0, hd, ?_⟩
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hAc.continuousOn
    (fun u hu => (hd u ⟨hu.1, hu.2.le.trans ht.2⟩).hasDerivWithinAt)
    (a := (0 : ℝ)) (b := t) (δ := 1) (ε := 0) (K := (K : ℝ))
    (by rw [hA0]; exact ContinuousLinearMap.norm_id_le)
    (fun u hu => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [add_zero] using mul_le_mul_of_nonneg_right (hB u) (norm_nonneg (A u))))
    t ⟨ht.1, le_rfl⟩
  simpa only [gronwallBound_ε0, one_mul, sub_zero] using hg

end Euler2D

end
