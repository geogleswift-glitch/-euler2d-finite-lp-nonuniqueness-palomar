module

public import RequestProject.Euler.BanachBackwardGraphTangency
public import RequestProject.Euler.BanachQuadraticRemainderDifference
public import RequestProject.Euler.BanachWeightedOrbitComparison

/-! Quadratic Lipschitz control for the actual contraction graph.
The comparison uses the same Green operator and the true C² remainder;
graph differentiability away from the origin is not an assumption. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem localWeightedBackwardGraph_quadratic_difference
    (F : E → E) (hF0 : F 0 = 0) (L P : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    {ρ a β C r δ B : ℝ} (hρ : 1 ≤ ρ) (hρa : ρ < a)
    (hβ : 0 ≤ β) (hβρ : β < ρ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hcomm : L.comp P = P.comp L) (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ C * β ^ k * ‖v‖)
    (hLip : ∀ z ∈ closedBall (0 : E) r, ∀ w ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder F z - banachLocalRemainder F w‖ ≤ δ * ‖z - w‖)
    (hquad : ∀ z ∈ closedBall (0 : E) r, ∀ w ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder F z - banachLocalRemainder F w‖ ≤ B * (‖z‖ + ‖w‖) * ‖z - w‖)
    (G : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E))
    (hGrec : ∀ (f : ℕ →ᵇ E) (n : ℕ), ρ • G f n = L (G f (n + 1)) + f (n + 1))
    (hGP : ∀ f : ℕ →ᵇ E, P (G f 0) = 0) (hsmall : ‖G‖ * δ ≤ 1 / 2)
    {x : E → ℕ → E} (hg : IsLocalWeightedBackwardGraph F P ρ r x)
    {ξ ζ : E} (hξ : P ξ = ξ) (hξr : ‖ξ‖ ≤ r / 2) (hζ : P ζ = ζ) (hζr : ‖ζ‖ ≤ r / 2) :
    ‖(x ξ 0 - ξ) - (x ζ 0 - ζ)‖ ≤
      (4 * ‖G‖ * B) * (‖ξ‖ + ‖ζ‖) * ‖ξ - ζ‖ := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hxn := hg.norm_le_radius hρ hξ hξr
  have hzn := hg.norm_le_radius hρ hζ hζr
  let u := boundedWeightedBackwardOrbit hρ hr (x ξ) hxn
  let v := boundedWeightedBackwardOrbit hρ hr (x ζ) hzn
  have hurec := boundedWeightedBackwardOrbit_recurrence F L hderiv hρ hr hδ hF0 hLip
    (x ξ) hxn (hg.backward ξ hξ hξr)
  have hvrec := boundedWeightedBackwardOrbit_recurrence F L hderiv hρ hr hδ hF0 hLip
    (x ζ) hzn (hg.backward ζ hζ hζr)
  let s := geometricBanachSequence (ρ / a) (div_nonneg hρ0.le (hρ0.trans hρa).le)
    ((div_lt_one (hρ0.trans hρa)).mpr hρa).le (ξ - ζ)
  have hs0 : s 0 = ξ - ζ := geometricBanachSequence_zero _ _ _ _
  have hs : ‖s‖ = ‖ξ - ζ‖ := norm_geometricBanachSequence _ _ _ _
  have hPdiff : P (ξ - ζ) = ξ - ζ := by rw [P.map_sub, hξ, hζ]
  have hLdiff : L (ξ - ζ) = a • (ξ - ζ) := by
    calc
      _ = L (P (ξ - ζ)) := congrArg L hPdiff.symm
      _ = a • P (ξ - ζ) := heigen _
      _ = _ := congrArg (fun z : E => a • z) hPdiff
  have hsrec := geometricBanachSequence_backward hρ0 hρa L (ξ - ζ) hLdiff
  have hu0 : u.val 0 = x ξ 0 := by
    simp only [u, boundedWeightedBackwardOrbit_apply, pow_zero, one_smul]
  have hv0 : v.val 0 = x ζ 0 := by
    simp only [v, boundedWeightedBackwardOrbit_apply, pow_zero, one_smul]
  have hsP : P (s 0) = P (u.val 0) - P (v.val 0) := by
    rw [hs0, hPdiff, hu0, hv0, hg.coordinate ξ hξ hξr, hg.coordinate ζ hζ hζr]
  obtain ⟨hid, hdist⟩ := weightedNonlinearSequence_affine_difference hρ (hρ0.trans hρa).ne'
    hβ hβρ hC hr hδ L P hcomm heigen hbound (banachLocalRemainder F)
    (banachLocalRemainder_zero hF0) hLip G hGrec hGP hsmall u v hurec hvrec s hsrec hsP
  rw [hs] at hdist
  have hnorm (a : E) (ha : P a = a) (har : ‖a‖ ≤ r / 2) :
      ‖(boundedWeightedBackwardOrbit hρ hr (x a) (hg.norm_le_radius hρ ha har)).val‖ ≤ 2 * ‖a‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ 2 * ‖a‖)).mpr
    intro n
    have hw := real_weight_inverse_pow_facts hρ n
    rw [boundedWeightedBackwardOrbit_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.1]
    calc
      _ ≤ ρ ^ n * (2 * (ρ⁻¹) ^ n * ‖a‖) :=
        mul_le_mul_of_nonneg_left (hg.norm_le a ha har n) hw.1
      _ = (ρ ^ n * (ρ⁻¹) ^ n) * (2 * ‖a‖) := by ring
      _ = _ := by rw [hw.2.2.2, one_mul]
  have hun : ‖u.val‖ ≤ 2 * ‖ξ‖ := hnorm ξ hξ hξr
  have hvn : ‖v.val‖ ≤ 2 * ‖ζ‖ := hnorm ζ hζ hζr
  let N := weightedSequenceRemainder hρ hr hδ (banachLocalRemainder_zero hF0) hLip
  have heval : u.val 0 - v.val 0 = s 0 + G (N u - N v) 0 :=
    congrArg (fun y : ℕ →ᵇ E => y 0) hid
  rw [hu0, hv0, hs0] at heval
  have herr : (x ξ 0 - ξ) - (x ζ 0 - ζ) = G (N u - N v) 0 := by
    calc
      _ = (x ξ 0 - x ζ 0) - (ξ - ζ) := by abel
      _ = _ := by rw [heval]; abel
  have hN : ‖N u - N v‖ ≤ B * (‖u.val‖ + ‖v.val‖) * ‖u.val - v.val‖ :=
    norm_weightedSequenceRemainder_sub_le_quadratic hρ hr hδ hB
      (banachLocalRemainder_zero hF0) hLip hquad u v
  rw [herr]
  calc
    _ ≤ ‖G (N u - N v)‖ := BoundedContinuousFunction.norm_coe_le_norm _ 0
    _ ≤ ‖G‖ * ‖N u - N v‖ := G.le_opNorm _
    _ ≤ ‖G‖ * (B * (‖u.val‖ + ‖v.val‖) * ‖u.val - v.val‖) :=
      mul_le_mul_of_nonneg_left hN (norm_nonneg G)
    _ ≤ ‖G‖ * (B * (2 * ‖ξ‖ + 2 * ‖ζ‖) * (2 * ‖ξ - ζ‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg G)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (add_le_add hun hvn) hB) hdist
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem exists_localWeightedBackwardGraph_quadraticLipschitz_of_kernel_bound
    (F : E → E) (hf : ContDiffAt ℝ 2 F 0) (hF0 : F 0 = 0)
    (L : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    {ρ a β C : ℝ} (hρ : 1 < ρ) (hρa : ρ < a) (hβ : 0 ≤ β) (hβρ : β < ρ) (hC : 0 ≤ C)
    (P : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) (hLP : L.comp P = P.comp L)
    (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ C * β ^ k * ‖v‖)
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ r > 0, r ≤ rmax ∧ ∃ x : E → ℕ → E,
      IsLocalWeightedBackwardGraph F P ρ r x ∧ ∃ H > 0,
      ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → ∀ ζ, P ζ = ζ → ‖ζ‖ ≤ r / 2 →
        ‖(x ξ 0 - ξ) - (x ζ 0 - ζ)‖ ≤ H * (‖ξ‖ + ‖ζ‖) * ‖ξ - ζ‖ := by
  letI : CompleteSpace P.ker := P.isClosed_ker.completeSpace_coe
  let A := invariantKernelCLM L P hLP
  let J : P.ker →L[ℝ] E := P.ker.subtypeL
  let Q := projectionComplementToKernelCLM P hP
  let G := hyperbolicSequenceGreenCLM ρ a A J Q P
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hA (k : ℕ) : ‖A ^ k‖ ≤ C * β ^ k :=
    norm_invariantKernelCLM_pow_le L P hLP hC hβ hbound k
  have hLJ (v : P.ker) : L (J v) = J (A v) := rfl
  have hJQ (v : E) : J (Q v) = v - P v := rfl
  have hPJ (v : P.ker) : P (J v) = 0 := v.property
  have hGrec (f : ℕ →ᵇ E) (n : ℕ) : ρ • G f n = L (G f (n + 1)) + f (n + 1) :=
    hyperbolicSequenceGreenCLM_recurrence hρ0 hρa hβ hβρ L A hA J Q P heigen hLJ hJQ f n
  have hGP (f : ℕ →ᵇ E) : P (G f 0) = 0 :=
    hyperbolicSequenceGreenCLM_projection_zero hρ0 hρa A J Q P hPJ f
  let δ := 1 / (2 * (‖G‖ + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hsmall : ‖G‖ * δ ≤ 1 / 2 := by
    have hd : δ * (2 * (‖G‖ + 1)) = 1 := by dsimp only [δ]; field_simp
    nlinarith [norm_nonneg G]
  have hf1 : ContDiffAt ℝ 1 F 0 := hf.of_le (by norm_num)
  obtain ⟨s, hs, hLip₀⟩ := exists_closedBall_lipschitz_banachLocalRemainder hf1 hδ
  obtain ⟨B, hB, q, hq, hquad₀⟩ := exists_banachLocalRemainder_quadratic_difference_bound hf
  obtain ⟨r, hr, hrr, x, hg, _⟩ := exists_localWeightedBackwardGraph_of_kernel_bound
    F hf1 hF0 L hderiv hρ hρa hβ hβρ hC P hP hLP heigen hbound
    (by norm_num : (0 : ℝ) < 1) (lt_min hrmax (lt_min hs hq))
  have hrs : r ≤ s := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrq : r ≤ q := hrr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLip : ∀ z ∈ closedBall (0 : E) r, ∀ w ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder F z - banachLocalRemainder F w‖ ≤ δ * ‖z - w‖ := by
    intro z hz w hw
    exact hLip₀ z (closedBall_subset_closedBall hrs hz) w (closedBall_subset_closedBall hrs hw)
  have hquad : ∀ z ∈ closedBall (0 : E) r, ∀ w ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder F z - banachLocalRemainder F w‖ ≤ B * (‖z‖ + ‖w‖) * ‖z - w‖ := by
    intro z hz w hw
    exact hquad₀ z (closedBall_subset_closedBall hrq hz) w (closedBall_subset_closedBall hrq hw)
  refine ⟨r, hr, hrr.trans (min_le_left _ _), x, hg, 4 * ‖G‖ * B + 1, by positivity, ?_⟩
  intro ξ hξ hξr ζ hζ hζr
  have hh := localWeightedBackwardGraph_quadratic_difference F hF0 L P hderiv hρ.le hρa
    hβ hβρ hC hr.le hδ.le hB.le hLP heigen hbound hLip hquad G hGrec hGP hsmall hg hξ hξr hζ hζr
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 4 * ‖G‖ * B ≤ 4 * ‖G‖ * B + 1)
      (by positivity : 0 ≤ ‖ξ‖ + ‖ζ‖)) (norm_nonneg _))

end Euler2D

end
