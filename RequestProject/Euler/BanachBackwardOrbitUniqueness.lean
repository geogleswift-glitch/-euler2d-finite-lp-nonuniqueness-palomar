module

public import RequestProject.Euler.BanachNonlinearKernelOrbit

/-! Uniqueness for the actual exponentially weighted backward equation.
The Green identity is recovered from its proved recurrence and the original
complement power bound, rather than assumed as an inverse property. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem bounded_weighted_homogeneous_backward_eq_zero
    {ρ a β C : ℝ} (hρ : 0 < ρ) (ha : a ≠ 0)
    (hβ : 0 ≤ β) (hβρ : β < ρ) (hC : 0 ≤ C)
    (L P : E →L[ℝ] E) (hcomm : L.comp P = P.comp L)
    (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ C * β ^ k * ‖v‖)
    (u : ℕ →ᵇ E) (hrec : ∀ n, ρ • u n = L (u (n + 1)))
    (hzero : P (u 0) = 0) : u = 0 := by
  have hc (v : E) : P (L v) = L (P v) :=
    (congrArg (fun A : E →L[ℝ] E => A v) hcomm).symm
  have hp (n : ℕ) : P (u n) = 0 := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      have hr := congrArg P (hrec n)
      rw [P.map_smul, ih, smul_zero, hc, heigen] at hr
      exact (smul_eq_zero.mp hr.symm).resolve_left ha
  have hi (n k : ℕ) : u n = (ρ⁻¹) ^ k • (L ^ k) (u (n + k)) := by
    induction k with
    | zero => simp only [pow_zero, one_smul, ContinuousLinearMap.one_apply, add_zero]
    | succ k ih =>
      have hr : u (n + k) = ρ⁻¹ • L (u (n + (k + 1))) := by
        have hz := congrArg (fun v : E => ρ⁻¹ • v) (hrec (n + k))
        simpa only [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, Nat.add_assoc] using hz
      rw [ih, hr, map_smul, smul_smul, pow_succ, pow_succ,
        ContinuousLinearMap.mul_apply]
  have hq0 : 0 ≤ β / ρ := div_nonneg hβ hρ.le
  have hq1 : β / ρ < 1 := (div_lt_one hρ).mpr hβρ
  apply BoundedContinuousFunction.ext
  intro n
  have hnorm (k : ℕ) : ‖u n‖ ≤ (C * ‖u‖) * (β / ρ) ^ k := by
    calc
      _ = ‖(ρ⁻¹) ^ k • (L ^ k) (u (n + k))‖ := congrArg norm (hi n k)
      _ = (ρ⁻¹) ^ k * ‖(L ^ k) (u (n + k))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hρ.le) k)]
      _ ≤ (ρ⁻¹) ^ k * (C * β ^ k * ‖u (n + k)‖) :=
        mul_le_mul_of_nonneg_left (hbound k _ (hp _)) (pow_nonneg (inv_nonneg.mpr hρ.le) k)
      _ ≤ (ρ⁻¹) ^ k * (C * β ^ k * ‖u‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm u _) (mul_nonneg hC (pow_nonneg hβ k)))
          (pow_nonneg (inv_nonneg.mpr hρ.le) k)
      _ = _ := by rw [div_pow, div_eq_mul_inv]; ring
  have ht : Tendsto (fun k : ℕ => (C * ‖u‖) * (β / ρ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C * ‖u‖)
  have hz : ‖u n‖ ≤ 0 := ge_of_tendsto' ht hnorm
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))

theorem weightedNonlinearSequence_backward_unique
    {ρ a β C r δ : ℝ} (hρ : 1 ≤ ρ) (ha : a ≠ 0)
    (hβ : 0 ≤ β) (hβρ : β < ρ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (L P : E →L[ℝ] E) (hcomm : L.comp P = P.comp L)
    (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ C * β ^ k * ‖v‖)
    (R : E → E) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (G : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E))
    (hGrec : ∀ (f : ℕ →ᵇ E) (n : ℕ), ρ • G f n = L (G f (n + 1)) + f (n + 1))
    (hGP : ∀ f : ℕ →ᵇ E, P (G f 0) = 0) (hsmall : ‖G‖ * δ ≤ 1 / 2)
    (u v : closedBall (0 : ℕ →ᵇ E) r)
    (hurec : ∀ n, ρ • u.val n = L (u.val (n + 1)) +
      weightedSequenceRemainder hρ hr hδ hR hLip u (n + 1))
    (hvrec : ∀ n, ρ • v.val n = L (v.val (n + 1)) +
      weightedSequenceRemainder hρ hr hδ hR hLip v (n + 1))
    (hproj : P (u.val 0) = P (v.val 0)) : u = v := by
  let N := weightedSequenceRemainder hρ hr hδ hR hLip
  let f : ℕ →ᵇ E := N u - N v
  let w : ℕ →ᵇ E := u.val - v.val - G f
  have hwrec (n : ℕ) : ρ • w n = L (w (n + 1)) := by
    change ρ • (u.val n - v.val n - G f n) =
      L (u.val (n + 1) - v.val (n + 1) - G f (n + 1))
    rw [smul_sub, smul_sub, hurec n, hvrec n, hGrec f n, L.map_sub, L.map_sub]
    change (L (u.val (n + 1)) + N u (n + 1)) -
      (L (v.val (n + 1)) + N v (n + 1)) -
      (L (G f (n + 1)) + (N u (n + 1) - N v (n + 1))) = _
    abel
  have hwP : P (w 0) = 0 := by
    change P (u.val 0 - v.val 0 - G f 0) = 0
    rw [map_sub, map_sub, hproj, sub_self, hGP, sub_self]
  have hw : w = 0 := bounded_weighted_homogeneous_backward_eq_zero
    (lt_of_lt_of_le zero_lt_one hρ) ha hβ hβρ hC L P hcomm heigen hbound w hwrec hwP
  have hdiff : u.val - v.val = G f := sub_eq_zero.mp hw
  have hN : ‖f‖ ≤ δ * ‖u.val - v.val‖ :=
    norm_weightedSequenceRemainder_sub_le hρ hr hδ hR hLip u v
  have hnorm : ‖u.val - v.val‖ ≤ (‖G‖ * δ) * ‖u.val - v.val‖ := by
    calc
      _ = ‖G f‖ := congrArg norm hdiff
      _ ≤ ‖G‖ * ‖f‖ := G.le_opNorm f
      _ ≤ ‖G‖ * (δ * ‖u.val - v.val‖) := mul_le_mul_of_nonneg_left hN (norm_nonneg G)
      _ = _ := by ring
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hh := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (u.val - v.val))
  nlinarith [norm_nonneg (u.val - v.val)]

def boundedWeightedBackwardOrbit {ρ r : ℝ} (hρ : 1 ≤ ρ) (hr : 0 ≤ r)
    (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ r * (ρ⁻¹) ^ n) :
    closedBall (0 : ℕ →ᵇ E) r := by
  let u : ℕ →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => ρ ^ n • x n) r (by
      intro n
      have hw := real_weight_inverse_pow_facts hρ n
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.1]
      calc
        _ ≤ ρ ^ n * (r * (ρ⁻¹) ^ n) := mul_le_mul_of_nonneg_left (hx n) hw.1
        _ = r := by nlinarith [hw.2.2.2])
  refine ⟨u, ?_⟩
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  exact (BoundedContinuousFunction.norm_le hr).mpr (fun n => by
    change ‖ρ ^ n • x n‖ ≤ r
    have hw := real_weight_inverse_pow_facts hρ n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.1]
    calc
      _ ≤ ρ ^ n * (r * (ρ⁻¹) ^ n) := mul_le_mul_of_nonneg_left (hx n) hw.1
      _ = r := by nlinarith [hw.2.2.2])

theorem boundedWeightedBackwardOrbit_apply {ρ r : ℝ} (hρ : 1 ≤ ρ) (hr : 0 ≤ r)
    (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ r * (ρ⁻¹) ^ n) (n : ℕ) :
    (boundedWeightedBackwardOrbit hρ hr x hx).val n = ρ ^ n • x n := rfl

theorem boundedWeightedBackwardOrbit_unweight {ρ r : ℝ} (hρ : 1 ≤ ρ) (hr : 0 ≤ r)
    (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ r * (ρ⁻¹) ^ n) (n : ℕ) :
    (ρ⁻¹) ^ n • (boundedWeightedBackwardOrbit hρ hr x hx).val n = x n := by
  rw [boundedWeightedBackwardOrbit_apply, smul_smul, mul_comm,
    (real_weight_inverse_pow_facts hρ n).2.2.2, one_smul]

theorem boundedWeightedBackwardOrbit_recurrence
    (F : E → E) (L : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    {ρ r δ : ℝ} (hρ : 1 ≤ ρ) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hF0 : F 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder F x - banachLocalRemainder F y‖ ≤ δ * ‖x - y‖)
    (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ r * (ρ⁻¹) ^ n)
    (hrec : ∀ n, F (x (n + 1)) = x n) (n : ℕ) :
    ρ • (boundedWeightedBackwardOrbit hρ hr x hx).val n =
      L ((boundedWeightedBackwardOrbit hρ hr x hx).val (n + 1)) +
        weightedSequenceRemainder hρ hr hδ (banachLocalRemainder_zero hF0) hLip
          (boundedWeightedBackwardOrbit hρ hr x hx) (n + 1) := by
  rw [weightedSequenceRemainder_apply, weightedSequenceRemainderValue,
    boundedWeightedBackwardOrbit_unweight, boundedWeightedBackwardOrbit_apply,
    boundedWeightedBackwardOrbit_apply, map_smul, ← smul_add]
  have hs : L (x (n + 1)) + banachLocalRemainder F (x (n + 1)) = F (x (n + 1)) := by
    rw [banachLocalRemainder, hderiv]
    abel
  rw [hs, hrec, smul_smul, pow_succ]
  congr 1
  ring

theorem banachBackwardOrbit_eq_of_small_remainder
    (F : E → E) (hF0 : F 0 = 0) (L P : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    {ρ a β C r δ : ℝ} (hρ : 1 ≤ ρ) (ha : a ≠ 0)
    (hβ : 0 ≤ β) (hβρ : β < ρ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hcomm : L.comp P = P.comp L) (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ C * β ^ k * ‖v‖)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder F x - banachLocalRemainder F y‖ ≤ δ * ‖x - y‖)
    (G : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E))
    (hGrec : ∀ (f : ℕ →ᵇ E) (n : ℕ), ρ • G f n = L (G f (n + 1)) + f (n + 1))
    (hGP : ∀ f : ℕ →ᵇ E, P (G f 0) = 0) (hsmall : ‖G‖ * δ ≤ 1 / 2)
    (x y : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ r * (ρ⁻¹) ^ n)
    (hy : ∀ n, ‖y n‖ ≤ r * (ρ⁻¹) ^ n)
    (hxrec : ∀ n, F (x (n + 1)) = x n) (hyrec : ∀ n, F (y (n + 1)) = y n)
    (hproj : P (x 0) = P (y 0)) : x = y := by
  have hu := boundedWeightedBackwardOrbit_recurrence F L hderiv hρ hr hδ hF0 hLip x hx hxrec
  have hv := boundedWeightedBackwardOrbit_recurrence F L hderiv hρ hr hδ hF0 hLip y hy hyrec
  have h0 : P ((boundedWeightedBackwardOrbit hρ hr x hx).val 0) =
      P ((boundedWeightedBackwardOrbit hρ hr y hy).val 0) := by
    simpa only [boundedWeightedBackwardOrbit_apply, pow_zero, one_smul] using hproj
  have heq := weightedNonlinearSequence_backward_unique hρ ha hβ hβρ hC hr hδ L P hcomm
    heigen hbound (banachLocalRemainder F) (banachLocalRemainder_zero hF0) hLip
    G hGrec hGP hsmall (boundedWeightedBackwardOrbit hρ hr x hx)
      (boundedWeightedBackwardOrbit hρ hr y hy) hu hv h0
  funext n
  have he := congrArg (fun u : closedBall (0 : ℕ →ᵇ E) r => (ρ⁻¹) ^ n • u.val n) heq
  simpa only [boundedWeightedBackwardOrbit_unweight] using he

end Euler2D

end
