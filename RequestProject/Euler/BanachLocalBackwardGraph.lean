module

public import RequestProject.Euler.BanachBackwardOrbitUniqueness

/-! A graph chosen from the actual weighted contraction has a unique
small backward orbit. Its shift identities follow from that uniqueness.
No smoothness or invariant-manifold theorem is used as an assumption. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

structure IsLocalWeightedBackwardGraph (F : E → E) (P : E →L[ℝ] E) (ρ r : ℝ)
    (x : E → ℕ → E) : Prop where
  backward : ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → ∀ n, F (x ξ (n + 1)) = x ξ n
  norm_le : ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → ∀ n,
    ‖x ξ n‖ ≤ 2 * (ρ⁻¹) ^ n * ‖ξ‖
  coordinate : ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → P (x ξ 0) = ξ
  unique : ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → ∀ y : ℕ → E,
    (∀ n, F (y (n + 1)) = y n) →
    (∀ n, ‖y n‖ ≤ r * (ρ⁻¹) ^ n) → P (y 0) = ξ → y = x ξ

theorem exists_localWeightedBackwardGraph_of_kernel_bound
    (F : E → E) (hf : ContDiffAt ℝ 1 F 0) (hF0 : F 0 = 0)
    (L : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    {ρ a β C : ℝ} (hρ : 1 < ρ) (hρa : ρ < a) (hβ : 0 ≤ β) (hβρ : β < ρ) (hC : 0 ≤ C)
    (P : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) (hLP : L.comp P = P.comp L)
    (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ C * β ^ k * ‖v‖)
    {ε rmax : ℝ} (hε : 0 < ε) (hrmax : 0 < rmax) :
    ∃ r > 0, r ≤ rmax ∧ ∃ x : E → ℕ → E,
      IsLocalWeightedBackwardGraph F P ρ r x ∧
      ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → ‖x ξ 0 - ξ‖ ≤ ε * ‖ξ‖ := by
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
    have hd : δ * (2 * (‖G‖ + 1)) = 1 := by
      dsimp only [δ]
      field_simp
    nlinarith [norm_nonneg G]
  obtain ⟨r₀, hr₀, hLip₀⟩ := exists_closedBall_lipschitz_banachLocalRemainder hf hδ
  obtain ⟨r, hr, hrr, hex⟩ := exists_banachBackwardOrbit_of_kernel_bound F hf hF0 L hderiv
    hρ hρa hβ hβρ hC P hP hLP heigen hbound hε (lt_min hr₀ hrmax)
  have hLip : ∀ z ∈ closedBall (0 : E) r, ∀ w ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder F z - banachLocalRemainder F w‖ ≤ δ * ‖z - w‖ := by
    intro z hz w hw
    exact hLip₀ z (closedBall_subset_closedBall (hrr.trans (min_le_left _ _)) hz)
      w (closedBall_subset_closedBall (hrr.trans (min_le_left _ _)) hw)
  have hchoice (ξ : E) : ∃ y : ℕ → E, P ξ = ξ → ‖ξ‖ ≤ r / 2 →
      (∀ n, F (y (n + 1)) = y n) ∧
      (∀ n, ‖y n‖ ≤ 2 * (ρ⁻¹) ^ n * ‖ξ‖) ∧
      P (y 0) = ξ ∧ ‖y 0 - ξ‖ ≤ ε * ‖ξ‖ := by
    by_cases hg : P ξ = ξ ∧ ‖ξ‖ ≤ r / 2
    · obtain ⟨y, hyrec, _, hynorm, hyproj, hyerror, _⟩ := hex ξ hg.1 hg.2
      exact ⟨y, fun _ _ => ⟨hyrec, hynorm, hyproj, hyerror⟩⟩
    · exact ⟨fun _ => 0, fun hξ hξr => False.elim (hg ⟨hξ, hξr⟩)⟩
  choose x hx using hchoice
  refine ⟨r, hr, hrr.trans (min_le_right _ _), x, ?_, ?_⟩
  · refine ⟨fun ξ hξ hξr => (hx ξ hξ hξr).1,
      fun ξ hξ hξr => (hx ξ hξ hξr).2.1,
      fun ξ hξ hξr => (hx ξ hξ hξr).2.2.1, ?_⟩
    intro ξ hξ hξr y hyrec hynorm hyproj
    have hxn (n : ℕ) : ‖x ξ n‖ ≤ r * (ρ⁻¹) ^ n := by
      have hp : 0 ≤ (ρ⁻¹) ^ n := pow_nonneg (inv_nonneg.mpr hρ0.le) n
      have hh := mul_le_mul_of_nonneg_right hξr hp
      have hn := (hx ξ hξ hξr).2.1 n
      nlinarith
    exact banachBackwardOrbit_eq_of_small_remainder F hF0 L P hderiv hρ.le
      (hρ0.trans hρa).ne' hβ hβρ hC hr.le hδ.le hLP heigen hbound hLip G hGrec hGP hsmall
      y (x ξ) hynorm hxn hyrec (hx ξ hξ hξr).1 (hyproj.trans (hx ξ hξ hξr).2.2.1.symm)
  · intro ξ hξ hξr
    exact (hx ξ hξ hξr).2.2.2

namespace IsLocalWeightedBackwardGraph

variable {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}

theorem norm_le_radius (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hρ : 1 ≤ ρ) {ξ : E} (hξ : P ξ = ξ) (hξr : ‖ξ‖ ≤ r / 2) (n : ℕ) :
    ‖x ξ n‖ ≤ r * (ρ⁻¹) ^ n := by
  have hp : 0 ≤ (ρ⁻¹) ^ n :=
    (real_weight_inverse_pow_facts hρ n).2.1
  have hh := mul_le_mul_of_nonneg_right hξr hp
  have hn := h.norm_le ξ hξ hξr n
  nlinarith

theorem backward_shift (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hρ : 1 ≤ ρ) (hP : ∀ v, P (P v) = P v)
    {ξ : E} (hξ : P ξ = ξ) (hξr : ‖ξ‖ ≤ r / 2)
    (hnext : ‖P (x ξ 1)‖ ≤ r / 2) :
    x (P (x ξ 1)) = fun n => x ξ (n + 1) := by
  symm
  apply h.unique _ (hP _) hnext
  · intro n
    exact h.backward ξ hξ hξr (n + 1)
  · intro n
    have hn := h.norm_le_radius hρ hξ hξr (n + 1)
    have hp := real_weight_inverse_pow_facts hρ 1
    have hr : 0 ≤ r := le_trans (by positivity : (0 : ℝ) ≤ 2 * ‖ξ‖) (by linarith)
    calc
      _ ≤ r * (ρ⁻¹) ^ (n + 1) := hn
      _ = (r * (ρ⁻¹) ^ n) * ρ⁻¹ := by rw [pow_succ]; ring
      _ ≤ (r * (ρ⁻¹) ^ n) * 1 := mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using hp.2.2.1)
        (mul_nonneg hr (real_weight_inverse_pow_facts hρ n).2.1)
      _ = _ := mul_one _
  · rfl

theorem zero (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hr : 0 ≤ r) : x 0 = 0 := by
  funext n
  have hn := h.norm_le 0 (map_zero P) (by simpa using div_nonneg hr (by norm_num : (0 : ℝ) ≤ 2)) n
  simpa only [Pi.zero_apply, norm_zero, mul_zero, norm_le_zero_iff] using hn

theorem forward_shift (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hρ : 1 ≤ ρ) (hP : ∀ v, P (P v) = P v)
    {ξ : E} (hξ : P ξ = ξ) (hξr : ‖ξ‖ ≤ r / 2)
    (hweighted : 2 * ρ * ‖ξ‖ ≤ r) (himage : ‖F (x ξ 0)‖ ≤ r)
    (hnext : ‖P (F (x ξ 0))‖ ≤ r / 2) :
    x (P (F (x ξ 0))) = fun n => Nat.casesOn n (F (x ξ 0)) (fun k => x ξ k) := by
  symm
  apply h.unique _ (hP _) hnext
  · intro n
    cases n with
    | zero => rfl
    | succ n => exact h.backward ξ hξ hξr n
  · intro n
    cases n with
    | zero =>
      change ‖F (x ξ 0)‖ ≤ r * (ρ⁻¹) ^ 0
      simpa only [pow_zero, mul_one] using himage
    | succ n =>
      change ‖x ξ n‖ ≤ r * (ρ⁻¹) ^ (n + 1)
      have hp := (real_weight_inverse_pow_facts hρ (n + 1)).2.1
      calc
        _ ≤ 2 * (ρ⁻¹) ^ n * ‖ξ‖ := h.norm_le ξ hξ hξr n
        _ = (2 * ρ * ‖ξ‖) * (ρ⁻¹) ^ (n + 1) := by
          rw [pow_succ]
          have hz : ρ ≠ 0 := (lt_of_lt_of_le zero_lt_one hρ).ne'
          field_simp
          <;> ring
        _ ≤ r * (ρ⁻¹) ^ (n + 1) := mul_le_mul_of_nonneg_right hweighted hp
  · rfl

end IsLocalWeightedBackwardGraph

end Euler2D

end
