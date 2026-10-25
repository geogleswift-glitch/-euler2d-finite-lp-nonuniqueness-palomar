module

public import RequestProject.Euler.BanachFiniteEndpointLimit
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Actual nonautonomous trajectories glue at a finite limiting
endpoint. The derivative at the join follows from the true one-sided
limits and the same vector field, rather than being assumed. -/

@[expose] public section

noncomputable section

open Set Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def concatenateAtEndpoint (α β : ℝ → E) (T : ℝ) (a : E) (t : ℝ) : E :=
  if t ≤ T then leftEndpointExtension α T a t else β (t - T)

theorem concatenateAtEndpoint_hasDerivAt {f : ℝ → E → E} {α β : ℝ → E}
    {T δ : ℝ} {a : E} (hT : 0 < T) (hδ : 0 ≤ δ)
    (hα : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt α (f t (α t)) t)
    (ha : Tendsto α (𝓝[<] T) (𝓝 a))
    (hfc : ContinuousAt (fun p : ℝ × E => f p.1 p.2) (T, a))
    (hβ0 : β 0 = a)
    (hβ : ∀ s ∈ Icc (0 : ℝ) δ, HasDerivAt β (f (T + s) (β s)) s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T + δ)) :
    HasDerivAt (concatenateAtEndpoint α β T a)
      (f t (concatenateAtEndpoint α β T a t)) t := by
  rcases lt_trichotomy t T with hlt | heq | hgt
  · have he : concatenateAtEndpoint α β T a =ᶠ[𝓝 t] α := by
      filter_upwards [eventually_lt_nhds hlt] with s hs
      simp only [concatenateAtEndpoint, if_pos hs.le, leftEndpointExtension, if_pos hs]
    simpa only [concatenateAtEndpoint, if_pos hlt.le, leftEndpointExtension, if_pos hlt] using
      (hα t ⟨ht.1, hlt⟩).congr_of_eventuallyEq he
  · subst t
    have hi : Tendsto (fun s : ℝ => s) (𝓝[<] T) (𝓝 T) := continuousWithinAt_id
    have harg : Tendsto (fun s : ℝ => (s, α s)) (𝓝[<] T) (𝓝 (T, a)) :=
      hi.prodMk_nhds ha
    have hflim : Tendsto (fun s => f s (α s)) (𝓝[<] T) (𝓝 (f T a)) :=
      hfc.tendsto.comp harg
    have hdleft := hasDerivWithinAt_leftEndpointExtension hT
      (fun s hs => hα s ⟨hs.1.le, hs.2⟩) ha hflim
    have hleft : HasDerivWithinAt (concatenateAtEndpoint α β T a) (f T a) (Iic T) T :=
      hdleft.congr (fun s hs => if_pos hs) (if_pos le_rfl)
    have hdright0 : HasDerivAt β (f T a) (T - T) := by
      simpa only [sub_self, add_zero, hβ0] using hβ 0 ⟨le_rfl, hδ⟩
    have hdright := hdright0.scomp T (h := fun s : ℝ => s - T) ((hasDerivAt_id T).sub_const T)
    simp only [one_smul] at hdright
    have he (s : ℝ) (hs : s ∈ Ici T) :
        concatenateAtEndpoint α β T a s = β (s - T) := by
      rcases eq_or_lt_of_le (mem_Ici.mp hs) with heq | hlt
      · subst s
        simp only [concatenateAtEndpoint, le_refl, if_true, leftEndpointExtension,
          lt_self_iff_false, if_false, sub_self, hβ0]
      · exact if_neg (not_le.mpr hlt)
    have hright : HasDerivWithinAt (concatenateAtEndpoint α β T a) (f T a) (Ici T) T :=
      hdright.hasDerivWithinAt.congr he (he T (mem_Ici.mpr le_rfl))
    have hboth := hleft.union hright
    have hu : Iic T ∪ Ici T = (univ : Set ℝ) := by
      ext s
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total s T
    rw [hu] at hboth
    simpa only [concatenateAtEndpoint, le_refl, if_true, leftEndpointExtension,
      lt_self_iff_false, if_false] using hboth.hasDerivAt Filter.univ_mem
  · have he : concatenateAtEndpoint α β T a =ᶠ[𝓝 t] fun s => β (s - T) := by
      filter_upwards [eventually_gt_nhds hgt] with s hs
      exact if_neg (not_le.mpr hs)
    have hdright := (hβ (t - T) ⟨by linarith, by linarith [ht.2]⟩).scomp t (h := fun s : ℝ => s - T)
      ((hasDerivAt_id t).sub_const T)
    have htime : T + (t - T) = t := by ring
    simp only [one_smul, htime] at hdright
    simpa only [concatenateAtEndpoint, if_neg (not_le.mpr hgt)] using
      hdright.congr_of_eventuallyEq he

theorem concatenateAtEndpoint_continuousOn {f : ℝ → E → E} {α β : ℝ → E}
    {T δ : ℝ} {a : E} (hT : 0 < T) (hδ : 0 ≤ δ)
    (hα : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt α (f t (α t)) t)
    (ha : Tendsto α (𝓝[<] T) (𝓝 a))
    (hfc : ContinuousAt (fun p : ℝ × E => f p.1 p.2) (T, a))
    (hβ0 : β 0 = a)
    (hβ : ∀ s ∈ Icc (0 : ℝ) δ, HasDerivAt β (f (T + s) (β s)) s) :
    ContinuousOn (concatenateAtEndpoint α β T a) (Icc (0 : ℝ) (T + δ)) := by
  intro t ht
  exact (concatenateAtEndpoint_hasDerivAt hT hδ hα ha hfc hβ0 hβ ht).continuousAt.continuousWithinAt

end Euler2D

end
