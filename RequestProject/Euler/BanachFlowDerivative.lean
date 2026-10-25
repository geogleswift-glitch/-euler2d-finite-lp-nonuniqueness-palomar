module

public import RequestProject.Euler.BanachFlowTaylor
public import RequestProject.Euler.BanachFlowVariational

/-! Actual initial-point linearization of Banach-space integral curves.
The family hypotheses consist only of its true time ODE, initial values
and membership in the genuine open field domain. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsBanachFlowOn (f : E → E) (U V : Set E) (T : ℝ) (X : E → ℝ → E) : Prop where
  initial : ∀ b ∈ V, X b 0 = b
  continuous : ∀ b ∈ V, ContinuousOn (X b) (Icc (0 : ℝ) T)
  hasDerivAt : ∀ b ∈ V, ∀ u ∈ Icc (0 : ℝ) T, HasDerivAt (X b) (f (X b u)) u
  mem : ∀ b ∈ V, ∀ u ∈ Icc (0 : ℝ) T, X b u ∈ U

namespace IsBanachFlowOn

theorem dist_le {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U V T X) {K : ℝ≥0} (hLip : LipschitzOnWith K f U)
    {b c : E} (hb : b ∈ V) (hc : c ∈ V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    dist (X b t) (X c t) ≤ dist b c * Real.exp ((K : ℝ) * t) := by
  have hd := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ : ℝ => f) (s := fun _ : ℝ => U) (K := K)
    (fun _ _ => hLip) (hX.continuous b hb)
    (fun u hu => (hX.hasDerivAt b hb u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => hX.mem b hb u ⟨hu.1, hu.2.le⟩)
    (hX.continuous c hc)
    (fun u hu => (hX.hasDerivAt c hc u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => hX.mem c hc u ⟨hu.1, hu.2.le⟩)
    (δ := dist b c) (by rw [hX.initial b hb, hX.initial c hc]) t ht
  simpa only [sub_zero] using hd

theorem norm_displacement_le {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U V T X) {K : ℝ≥0} (hLip : LipschitzOnWith K f U)
    {a h : E} (ha : a ∈ V) (hah : a + h ∈ V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X (a + h) t - X a t‖ ≤ Real.exp ((K : ℝ) * T) * ‖h‖ := by
  have hd : ‖X (a + h) t - X a t‖ ≤ ‖h‖ * Real.exp ((K : ℝ) * t) := by
    simpa only [dist_eq_norm, add_sub_cancel_left] using hX.dist_le hLip hah ha ht
  exact hd.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)) (norm_nonneg h)).trans_eq (mul_comm _ _))

end IsBanachFlowOn

def banachFlowLinearizationError (X : E → ℝ → E) (a h : E)
    (A : ℝ → E →L[ℝ] E) (t : ℝ) : E := X (a + h) t - X a t - A t h

theorem banachFlowLinearizationError_hasDerivAt
    {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U V T X) {a h : E} (ha : a ∈ V) (hah : a + h ∈ V)
    {A : ℝ → E →L[ℝ] E} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hAd : HasDerivAt A ((fderiv ℝ f (X a t)).comp (A t)) t) :
    HasDerivAt (banachFlowLinearizationError X a h A)
      (fderiv ℝ f (X a t) (banachFlowLinearizationError X a h A t) +
        (f (X (a + h) t) - f (X a t) - fderiv ℝ f (X a t) (X (a + h) t - X a t))) t := by
  have hd := (hX.hasDerivAt (a + h) hah t ht).sub (hX.hasDerivAt a ha t ht)
  have hAh := hAd.clm_apply (hasDerivAt_const t h)
  simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero] at hAh
  convert hd.sub hAh using 1 <;>
    (try funext s) <;>
    (try simp only [banachFlowLinearizationError, Pi.sub_def, map_sub]) <;> abel

private lemma banachFlow_gronwallBound_zero_mul (K c t : ℝ) :
    gronwallBound 0 K c t = c * gronwallBound 0 K 1 t := by
  unfold gronwallBound
  split_ifs <;> ring

theorem banachFlow_linearization_small
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {a : E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 ≤ T) {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U (ball a ρ) T X)
    {A : ℝ → E →L[ℝ] E} (hAc : ContinuousOn A (Icc (0 : ℝ) T))
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hAd : ∀ u ∈ Icc (0 : ℝ) T,
      HasDerivAt A ((fderiv ℝ f (X a u)).comp (A u)) u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : E, ‖h‖ ≤ δ → ‖banachFlowLinearizationError X a h A t‖ ≤ ε * ‖h‖ := by
  have ha : a ∈ ball a ρ := mem_ball_self hρ
  let P : ℝ := Real.exp ((K : ℝ) * T)
  let C : ℝ := |gronwallBound 0 (K : ℝ) 1 t| + 1
  have hP : 0 < P := Real.exp_pos _
  have hC : 0 < C := by dsimp only [C]; positivity
  let η : ℝ := ε / (P * C)
  have hη : 0 < η := div_pos hε (mul_pos hP hC)
  let x : ℝ → E := fun u => X a (Set.projIcc (0 : ℝ) T hT u)
  have hxc : Continuous x :=
    (hX.continuous a ha).restrict.comp (continuous_projIcc (h := hT))
  have hx (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : x u = X a u := by
    dsimp only [x]
    rw [Set.projIcc_of_mem _ hu]
  obtain ⟨d, hd, hTaylor⟩ := banachFlow_uniform_taylor_remainder hU hf isCompact_Icc hxc
    (fun u hu => by rw [hx u hu]; exact hX.mem a ha u hu) hη
  refine ⟨min (ρ / 2) (d / P), lt_min (half_pos hρ) (div_pos hd hP), ?_⟩
  intro h hh
  have hah : a + h ∈ ball a ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hh.trans (min_le_left _ _)).trans_lt (half_lt_self hρ)
  have hdisp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      ‖X (a + h) u - X a u‖ ≤ P * ‖h‖ := hX.norm_displacement_le hLip ha hah hu
  have hrem (u : ℝ) (hu : u ∈ Ico (0 : ℝ) t) :
      ‖f (X (a + h) u) - f (X a u) - fderiv ℝ f (X a u) (X (a + h) u - X a u)‖ ≤ η * P * ‖h‖ := by
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.le.trans ht.2⟩
    have hsmall : ‖X (a + h) u - X a u‖ ≤ d :=
      (hdisp u huT).trans (by
        have hh' := (le_div_iff₀ hP).mp (hh.trans (min_le_right _ _))
        simpa only [mul_comm] using hh')
    have hTayloru := (hTaylor u huT (X (a + h) u - X a u) hsmall).2
    rw [hx u huT] at hTayloru
    have he : X a u + (X (a + h) u - X a u) = X (a + h) u := by abel
    rw [he] at hTayloru
    exact hTayloru.trans (by nlinarith [hdisp u huT])
  have hsubset : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hu => ⟨hu.1, hu.2.trans ht.2⟩
  have hec : ContinuousOn (banachFlowLinearizationError X a h A) (Icc (0 : ℝ) t) :=
    (((hX.continuous (a + h) hah).sub (hX.continuous a ha)).sub
      (hAc.clm_apply continuousOn_const)).mono hsubset
  have he0 : banachFlowLinearizationError X a h A 0 = 0 := by
    simp only [banachFlowLinearizationError, hX.initial (a + h) hah, hX.initial a ha,
      hA0, ContinuousLinearMap.id_apply, add_sub_cancel_left, sub_self]
  have herr := norm_le_gronwallBound_of_norm_deriv_right_le hec
    (fun u hu => (banachFlowLinearizationError_hasDerivAt hX ha hah
      ⟨hu.1, hu.2.le.trans ht.2⟩ (hAd u ⟨hu.1, hu.2.le.trans ht.2⟩)).hasDerivWithinAt)
    (a := (0 : ℝ)) (b := t) (δ := 0) (ε := η * P * ‖h‖) (K := (K : ℝ))
    (by rw [he0, norm_zero])
    (fun u hu => by
      have hB : ‖fderiv ℝ f (X a u)‖ ≤ K :=
        norm_fderiv_le_of_lipschitzOn ℝ
          (hU.mem_nhds (hX.mem a ha u ⟨hu.1, hu.2.le.trans ht.2⟩)) hLip
      exact (norm_add_le _ _).trans ((add_le_add
        (((fderiv ℝ f (X a u)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))) (hrem u hu))))
    t ⟨ht.1, le_rfl⟩
  have hcoeff : gronwallBound 0 (K : ℝ) 1 t ≤ C :=
    (le_abs_self _).trans (by dsimp only [C]; linarith [abs_nonneg (gronwallBound 0 (K : ℝ) 1 t)])
  calc
    _ ≤ gronwallBound 0 (K : ℝ) (η * P * ‖h‖) t := by simpa only [sub_zero] using herr
    _ = (η * P * ‖h‖) * gronwallBound 0 (K : ℝ) 1 t := banachFlow_gronwallBound_zero_mul _ _ _
    _ ≤ (η * P * ‖h‖) * C := mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = ε * ‖h‖ := by dsimp only [η]; field_simp

theorem hasFDerivAt_banachFlow_of_variational
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {a : E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 ≤ T) {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U (ball a ρ) T X)
    {A : ℝ → E →L[ℝ] E} (hAc : ContinuousOn A (Icc (0 : ℝ) T))
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hAd : ∀ u ∈ Icc (0 : ℝ) T, HasDerivAt A ((fderiv ℝ f (X a u)).comp (A u)) u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt (fun b => X b t) (A t) a := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, herror⟩ := banachFlow_linearization_small hU hf hLip hρ hT hX hAc hA0 hAd ht hε
  filter_upwards [ball_mem_nhds (0 : E) hδ] with h hh
  exact herror h (show ‖h‖ < δ by simpa only [mem_ball, dist_zero_right] using hh).le

end Euler2D

end
