module

public import RequestProject.Euler.BanachFlowRegularity

/-! Concatenation of actual Banach ODE flows. The time derivative at
the joining point is proved from both one-sided derivatives. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def concatenateBanachFlows (X Y : E → ℝ → E) (T : ℝ) (b : E) (t : ℝ) : E :=
  if t ≤ T then X b t else Y (X b T) (t - T)

theorem concatenateBanachFlows_hasDerivAt
    {f : E → E} {U V W : Set E} {T S : ℝ} {X Y : E → ℝ → E}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hX : IsBanachFlowOn f U V T X)
    (hY : IsBanachFlowOn f U W S Y) (hmap : MapsTo (fun b => X b T) V W)
    {b : E} (hb : b ∈ V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T + S)) :
    HasDerivAt (concatenateBanachFlows X Y T b)
      (f (concatenateBanachFlows X Y T b t)) t := by
  have hbW := hmap hb
  have hjoin : Y (X b T) 0 = X b T := hY.initial _ hbW
  rcases lt_trichotomy t T with hlt | heq | hgt
  · have he : concatenateBanachFlows X Y T b =ᶠ[𝓝 t] X b := by
      filter_upwards [eventually_lt_nhds hlt] with s hs
      exact if_pos hs.le
    simpa only [concatenateBanachFlows, if_pos hlt.le] using
      (hX.hasDerivAt b hb t ⟨ht.1, hlt.le⟩).congr_of_eventuallyEq he
  · subst t
    have hx := (hX.hasDerivAt b hb T ⟨hT, le_rfl⟩).hasDerivWithinAt (s := Iic T)
    have hleft : HasDerivWithinAt (concatenateBanachFlows X Y T b)
        (f (X b T)) (Iic T) T := hx.congr (fun s hs => if_pos hs) (if_pos le_rfl)
    have hy0 : HasDerivAt (Y (X b T)) (f (X b T)) (T - T) := by
      simpa only [sub_self, hjoin] using hY.hasDerivAt (X b T) hbW 0 ⟨le_rfl, hS⟩
    have hy := hy0.scomp T (h := fun s : ℝ => s - T)
      ((hasDerivAt_id T).sub_const T)
    simp only [sub_self, one_smul, hjoin] at hy
    have he (s : ℝ) (hs : s ∈ Ici T) :
        concatenateBanachFlows X Y T b s = Y (X b T) (s - T) := by
      rcases eq_or_lt_of_le (mem_Ici.mp hs) with heq | hlt
      · subst s
        simp only [concatenateBanachFlows, le_refl, if_true, sub_self, hjoin]
      · exact if_neg (not_le.mpr hlt)
    have hright : HasDerivWithinAt (concatenateBanachFlows X Y T b)
        (f (X b T)) (Ici T) T :=
      hy.hasDerivWithinAt.congr he (he T (mem_Ici.mpr le_rfl))
    have hboth := hleft.union hright
    have hu : Iic T ∪ Ici T = (univ : Set ℝ) := by
      ext s
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total s T
    rw [hu] at hboth
    simpa only [concatenateBanachFlows, le_refl, if_true] using hboth.hasDerivAt Filter.univ_mem
  · have he : concatenateBanachFlows X Y T b =ᶠ[𝓝 t] fun s => Y (X b T) (s - T) := by
      filter_upwards [eventually_gt_nhds hgt] with s hs
      exact if_neg (not_le.mpr hs)
    have hy := (hY.hasDerivAt (X b T) hbW (t - T) ⟨by linarith, by linarith [ht.2]⟩).scomp t
      ((hasDerivAt_id t).sub_const T)
    simp only [one_smul] at hy
    simpa only [concatenateBanachFlows, if_neg (not_le.mpr hgt)] using hy.congr_of_eventuallyEq he

theorem IsBanachFlowOn.concatenate
    {f : E → E} {U V W : Set E} {T S : ℝ} {X Y : E → ℝ → E}
    (hX : IsBanachFlowOn f U V T X) (hY : IsBanachFlowOn f U W S Y)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hmap : MapsTo (fun b => X b T) V W) :
    IsBanachFlowOn f U V (T + S) (concatenateBanachFlows X Y T) := by
  have hd (b : E) (hb : b ∈ V) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (T + S)) :=
    concatenateBanachFlows_hasDerivAt hT hS hX hY hmap hb ht
  refine ⟨?_, ?_, fun b hb t ht => hd b hb t ht, ?_⟩
  · intro b hb
    simp only [concatenateBanachFlows, if_pos hT, hX.initial b hb]
  · intro b hb t ht
    exact (hd b hb t ht).continuousAt.continuousWithinAt
  · intro b hb t ht
    by_cases htT : t ≤ T
    · simpa only [concatenateBanachFlows, if_pos htT] using hX.mem b hb t ⟨ht.1, htT⟩
    · simpa only [concatenateBanachFlows, if_neg htT] using
        hY.mem (X b T) (hmap hb) (t - T) ⟨by linarith, by linarith [ht.2]⟩

theorem contDiffOn_concatenateBanachFlows
    {V W : Set E} {T S : ℝ} {X Y : E → ℝ → E} {n : ℕ}
    (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, ContDiffOn ℝ n (fun b => X b t) V)
    (hY : ∀ t ∈ Icc (0 : ℝ) S, ContDiffOn ℝ n (fun b => Y b t) W)
    (hmap : MapsTo (fun b => X b T) V W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T + S)) :
    ContDiffOn ℝ n (fun b => concatenateBanachFlows X Y T b t) V := by
  by_cases htT : t ≤ T
  · simpa only [concatenateBanachFlows, if_pos htT] using hX t ⟨ht.1, htT⟩
  · simpa only [concatenateBanachFlows, if_neg htT, Function.comp_def] using
      (hY (t - T) ⟨by linarith, by linarith [ht.2]⟩).comp (hX T ⟨hT, le_rfl⟩) hmap

end Euler2D

end
