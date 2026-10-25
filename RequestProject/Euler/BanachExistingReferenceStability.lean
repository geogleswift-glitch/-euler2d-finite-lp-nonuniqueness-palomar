module

public import RequestProject.Euler.BanachCompactLipschitzNeighborhood
public import RequestProject.Euler.BanachExistingForcedTrajectoryComparison
public import RequestProject.Euler.ContinuousCaptureSection

/-! Stability along a fixed compact reference arc for an already
existing forced curve. The curve's membership in the comparison tube
is proved by a first-exit argument, not supplied as a future hypothesis. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem dist_existing_forcedCurve_reference_le
    {f : E → E} {U : Set E} {K : ℝ≥0} {T δ ε : ℝ}
    {y c p : ℝ → E} (hε : 0 ≤ ε) (hLip : LipschitzOnWith K f U)
    (hyc : ContinuousOn y (Icc (0 : ℝ) T)) (hcc : ContinuousOn c (Icc (0 : ℝ) T))
    (hyd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt y (f (y t) + p t) t)
    (hcd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt c (f (c t)) t)
    (hym : ∀ t ∈ Icc (0 : ℝ) T, y t ∈ U)
    (hcm : ∀ t ∈ Icc (0 : ℝ) T, c t ∈ U)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, ‖p t‖ ≤ ε)
    (hinit : dist (y 0) (c 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      dist (y t) (c t) ≤ (δ + ε * t) * Real.exp ((K : ℝ) * t) := by
  intro t ht
  have hh := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun _ z => f z) (s := fun _ => U) (K := K)
    (fun _ _ => hLip) hyc
    (fun u hu => (hyd u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (εf := ε) (fun u hu => by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hp u ⟨hu.1, hu.2.le⟩)
    (fun u hu => hym u ⟨hu.1, hu.2.le⟩) hcc
    (fun u hu => (hcd u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (εg := 0) (fun _ _ => by simp)
    (fun u hu => hcm u ⟨hu.1, hu.2.le⟩) (δ := δ) hinit t ht
  have hh' : dist (y t) (c t) ≤ gronwallBound δ (K : ℝ) ε t := by
    simpa only [add_zero, sub_zero] using hh
  exact hh'.trans (gronwallBound_le_add_mul_exp K.coe_nonneg hε ht.1)

theorem exists_existing_compact_reference_stability_constants
    {f : E → E} {D : Set E} (hD : IsOpen D) (hf : ContDiffOn ℝ 1 f D)
    {T : ℝ} (hT : 0 < T) {c : ℝ → E}
    (hcc : ContinuousOn c (Icc (0 : ℝ) T))
    (hcd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt c (f (c t)) t)
    (hcm : ∀ t ∈ Icc (0 : ℝ) T, c t ∈ D) :
    ∃ r > 0, ∃ δ > 0, ∃ η > 0, ∃ K : ℝ≥0,
      ∀ {H ε : ℝ}, 0 ≤ H → H ≤ T → 0 ≤ ε → ε ≤ η →
      ∀ y p : ℝ → E,
        ContinuousOn y (Icc (0 : ℝ) H) →
        (∀ t ∈ Icc (0 : ℝ) H, HasDerivAt y (f (y t) + p t) t) →
        (∀ t ∈ Icc (0 : ℝ) H, ‖p t‖ ≤ ε) →
        dist (y 0) (c 0) ≤ δ →
        (∀ t ∈ Icc (0 : ℝ) H, dist (y t) (c t) < r) ∧
        (∀ t ∈ Icc (0 : ℝ) H,
          dist (y t) (c t) ≤ (dist (y 0) (c 0) + ε * t) * Real.exp ((K : ℝ) * t)) := by
  have hcompact : IsCompact (c '' Icc (0 : ℝ) T) := isCompact_Icc.image_of_continuousOn hcc
  have hsubset : c '' Icc (0 : ℝ) T ⊆ D := by
    rintro z ⟨t, ht, rfl⟩
    exact hcm t ht
  obtain ⟨U, hU, hcU, hUD, K, hLip⟩ :=
    exists_lipschitz_open_neighborhood_of_compact hD hf hcompact hsubset
  obtain ⟨r, hr, hrU⟩ := hcompact.exists_cthickening_subset_open hU hcU
  have htube (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : closedBall (c t) r ⊆ U :=
    (closedBall_subset_cthickening (mem_image_of_mem c ht) r).trans hrU
  have hcmU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : c t ∈ U :=
    hcU (mem_image_of_mem c ht)
  let C := Real.exp ((K : ℝ) * T)
  have hC : 0 < C := Real.exp_pos _
  have hC1 : 1 ≤ C := Real.one_le_exp_iff.mpr (mul_nonneg K.coe_nonneg hT.le)
  let δ := r / (4 * C)
  let η := δ / T
  have hδ : 0 < δ := div_pos hr (by positivity)
  have hη : 0 < η := div_pos hδ hT
  have hδC : δ * C = r / 4 := by
    dsimp only [δ]
    field_simp [hC.ne']
  have hηT : η * T = δ := div_mul_cancel₀ δ hT.ne'
  have hδr : δ < r := by
    have hh : δ ≤ δ * C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hC1 hδ.le
    rw [hδC] at hh
    linarith only [hh, hr]
  refine ⟨r, hr, δ, hδ, η, hη, K, ?_⟩
  intro H ε hH hHT hε hεη y p hyc hyd hp hinit
  have hbudget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (δ + ε * t) * Real.exp ((K : ℝ) * t) < r := by
    have he : Real.exp ((K : ℝ) * t) ≤ C :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)
    have hs : δ + ε * t ≤ δ + η * T :=
      add_le_add le_rfl (mul_le_mul hεη ht.2 ht.1 hη.le)
    have hh := mul_le_mul hs he (Real.exp_pos _).le (by positivity : 0 ≤ δ + η * T)
    rw [hηT] at hh
    nlinarith only [hh, hδC, hr]
  have hconfine (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : dist (y t) (c t) < r := by
    by_contra hbad
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) H := Icc_subset_Icc_right ht.2
    have hsubT : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc_right (ht.2.trans hHT)
    obtain ⟨τ, hτ, hvalue, hfirst⟩ := exists_first_continuous_norm_section ht.1
      (fun u => y u - c u) ((hyc.mono hsub).sub (hcc.mono hsubT))
      (by simpa only [dist_eq_norm] using hinit.trans_lt hδr)
      (by simpa only [dist_eq_norm] using not_lt.mp hbad)
    have hτH : τ ≤ H := hτ.2.trans ht.2
    have hτT : τ ≤ T := hτH.trans hHT
    have hτeq : dist (y τ) (c τ) = r := by simpa only [dist_eq_norm] using hvalue
    have hymτ (u : ℝ) (hu : u ∈ Icc (0 : ℝ) τ) : y u ∈ U := by
      apply htube u ⟨hu.1, hu.2.trans hτT⟩
      apply mem_closedBall.mpr
      by_cases heu : u = τ
      · simpa only [heu] using hτeq.le
      · simpa only [dist_eq_norm] using (hfirst u ⟨hu.1, lt_of_le_of_ne hu.2 heu⟩).le
    have hh := dist_existing_forcedCurve_reference_le hε hLip
      (hyc.mono (Icc_subset_Icc_right hτH)) (hcc.mono (Icc_subset_Icc_right hτT))
      (fun u hu => hyd u ⟨hu.1, hu.2.trans hτH⟩)
      (fun u hu => hcd u ⟨hu.1, hu.2.trans hτT⟩) hymτ
      (fun u hu => hcmU u ⟨hu.1, hu.2.trans hτT⟩)
      (fun u hu => hp u ⟨hu.1, hu.2.trans hτH⟩) hinit τ ⟨hτ.1.le, le_rfl⟩
    have hlt := hh.trans_lt (hbudget τ ⟨hτ.1.le, hτT⟩)
    exact (not_lt_of_ge hτeq.ge) hlt
  refine ⟨hconfine, ?_⟩
  exact dist_existing_forcedCurve_reference_le hε hLip hyc (hcc.mono (Icc_subset_Icc_right hHT))
    hyd (fun t ht => hcd t ⟨ht.1, ht.2.trans hHT⟩)
    (fun t ht => htube t ⟨ht.1, ht.2.trans hHT⟩ (mem_closedBall.mpr (hconfine t ht).le))
    (fun t ht => hcmU t ⟨ht.1, ht.2.trans hHT⟩) hp le_rfl

end Euler2D

end
