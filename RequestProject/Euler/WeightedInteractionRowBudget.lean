module

public import RequestProject.Euler.BanachWeightedTrajectoryEnvelope

/-! The actual sixth- and second-ratio row estimates close in the
same finite weighted norm, with constants uniform in the cutoff. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

noncomputable section

open Set
open scoped BigOperators NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_inner_row_sum_bound {b C₀ ρ : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hC₀ : 1 < C₀) (hρ : 0 < ρ)
    (k : ℕ) (x : ℕ → E) (j : Fin k) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin k => j < l),
      b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖) ≤
      (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
        (b / (C₀ - 1) * weightedFamilyNorm (C₀ * ρ ^ 6) k x) := by
  let h := C₀ * ρ ^ 6
  let Z := weightedFamilyNorm h k x
  have hC : 0 < C₀ := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hZ : 0 ≤ Z := norm_nonneg _
  have hterm (l : Fin k) (hl : l ∈ Finset.univ.filter (fun l : Fin k => j < l)) :
      b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖ ≤
        h ^ (k - (j : ℕ)) * (b * Z) * (C₀⁻¹) ^ ((l : ℕ) - j) := by
    have hjl : j < l := (Finset.mem_filter.mp hl).2
    have hn := norm_le_weightedFamilyNorm hh k x l
    have hbpow : b ^ (k - (l : ℕ)) ≤ b := by
      simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ k - (l : ℕ) by omega)
    have hid := rho_pow_up (ρ := ρ) hC.ne' (k - (l : ℕ)) ((l : ℕ) - j)
    rw [show k - (l : ℕ) + ((l : ℕ) - j) = k - (j : ℕ) by omega] at hid
    calc
      _ ≤ (b * ρ ^ (6 * ((l : ℕ) - j))) * (h ^ (k - (l : ℕ)) * Z) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hbpow (by positivity)) hn (norm_nonneg _) (by positivity)
      _ = b * Z * (ρ ^ (6 * ((l : ℕ) - j)) * (C₀ * ρ ^ 6) ^ (k - (l : ℕ))) := by dsimp [h]; ring
      _ = _ := by rw [hid]; dsimp [h]; ring
  have hgeo := sum_pow_le_of_injOn (Finset.univ.filter (fun l : Fin k => j < l))
    (fun l => (l : ℕ) - j)
    (fun a ha b' hb' hab => by
      have hja : (j : ℕ) < (a : ℕ) := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hjb : (j : ℕ) < (b' : ℕ) := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2
      change (a : ℕ) - (j : ℕ) = (b' : ℕ) - (j : ℕ) at hab
      exact Fin.ext (by omega))
    (fun l hl => by
      have hjl : (j : ℕ) < (l : ℕ) := (Finset.mem_filter.mp hl).2
      change 1 ≤ (l : ℕ) - (j : ℕ)
      omega)
    (inv_nonneg.mpr hC.le) (inv_lt_one_of_one_lt₀ hC₀)
  have heq : C₀⁻¹ / (1 - C₀⁻¹) = 1 / (C₀ - 1) := by field_simp
  rw [heq] at hgeo
  calc
    _ ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin k => j < l),
        h ^ (k - (j : ℕ)) * (b * Z) * (C₀⁻¹) ^ ((l : ℕ) - j) := Finset.sum_le_sum hterm
    _ = h ^ (k - (j : ℕ)) * (b * Z) *
        ∑ l ∈ Finset.univ.filter (fun l : Fin k => j < l), (C₀⁻¹) ^ ((l : ℕ) - j) := by rw [Finset.mul_sum]
    _ ≤ h ^ (k - (j : ℕ)) * (b * Z) * (1 / (C₀ - 1)) :=
      mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = _ := by dsimp [h, Z]; ring

theorem weighted_outer_row_sum_bound {b C₀ ρ : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hC₀ : 1 < C₀) (hρ : 0 < ρ)
    (hζ : C₀ * ρ ^ 8 < 1) (k : ℕ) (x : ℕ → E) (j : Fin k) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j),
      b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖) ≤
      (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
        (b * ((C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8)) * weightedFamilyNorm (C₀ * ρ ^ 6) k x) := by
  let h := C₀ * ρ ^ 6
  let Z := weightedFamilyNorm h k x
  let ζ := C₀ * ρ ^ 8
  have hC : 0 < C₀ := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hZ : 0 ≤ Z := norm_nonneg _
  have hζ0 : 0 ≤ ζ := by dsimp [ζ]; positivity
  have hterm (l : Fin k) (hl : l ∈ Finset.univ.filter (fun l : Fin k => l < j)) :
      b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖ ≤
        h ^ (k - (j : ℕ)) * (b * Z) * ζ ^ ((j : ℕ) - l) := by
    have hlj : l < j := (Finset.mem_filter.mp hl).2
    have hn := norm_le_weightedFamilyNorm hh k x l
    have hbpow : b ^ (k - (l : ℕ)) ≤ b := by
      simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ k - (l : ℕ) by omega)
    have hid := rho_pow_down C₀ ρ (k - (j : ℕ)) ((j : ℕ) - l)
    rw [show k - (j : ℕ) + ((j : ℕ) - l) = k - (l : ℕ) by omega] at hid
    calc
      _ ≤ (b * ρ ^ (2 * ((j : ℕ) - l))) * (h ^ (k - (l : ℕ)) * Z) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hbpow (by positivity)) hn (norm_nonneg _) (by positivity)
      _ = b * Z * (ρ ^ (2 * ((j : ℕ) - l)) * (C₀ * ρ ^ 6) ^ (k - (l : ℕ))) := by dsimp [h]; ring
      _ = _ := by rw [hid]; dsimp [h, ζ]; ring
  have hgeo := sum_pow_le_of_injOn (Finset.univ.filter (fun l : Fin k => l < j))
    (fun l => (j : ℕ) - l)
    (fun a ha b' hb' hab => by
      have haj : (a : ℕ) < (j : ℕ) := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hbj : (b' : ℕ) < (j : ℕ) := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2
      change (j : ℕ) - (a : ℕ) = (j : ℕ) - (b' : ℕ) at hab
      exact Fin.ext (by omega))
    (fun l hl => by
      have hlj : (l : ℕ) < (j : ℕ) := (Finset.mem_filter.mp hl).2
      change 1 ≤ (j : ℕ) - (l : ℕ)
      omega) hζ0 hζ
  calc
    _ ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j),
        h ^ (k - (j : ℕ)) * (b * Z) * ζ ^ ((j : ℕ) - l) := Finset.sum_le_sum hterm
    _ = h ^ (k - (j : ℕ)) * (b * Z) *
        ∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j), ζ ^ ((j : ℕ) - l) := by rw [Finset.mul_sum]
    _ ≤ h ^ (k - (j : ℕ)) * (b * Z) * (ζ / (1 - ζ)) :=
      mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = _ := by dsimp [h, Z, ζ]; ring

def weightedInteractionRowFeedback (b Cup Cdown C₀ ρ : ℝ) : ℝ :=
  b * (Cup / (C₀ - 1) + Cdown * (C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8))

theorem weightedInteractionRowFeedback_nonneg {b Cup Cdown C₀ ρ : ℝ}
    (hb : 0 ≤ b) (hup : 0 ≤ Cup) (hdown : 0 ≤ Cdown)
    (hC₀ : 1 < C₀) (hζ : C₀ * ρ ^ 8 < 1) :
    0 ≤ weightedInteractionRowFeedback b Cup Cdown C₀ ρ := by
  have hC : 0 < C₀ := by linarith
  have hpow : 0 ≤ ρ ^ 8 := by positivity
  unfold weightedInteractionRowFeedback
  exact mul_nonneg hb (add_nonneg
    (div_nonneg hup (by linarith))
    (div_nonneg (mul_nonneg hdown (mul_nonneg hC.le hpow)) (by linarith)))

theorem weighted_interaction_row_source_bound {b Cup Cdown C₀ ρ β₀ g : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hup : 0 ≤ Cup) (hdown : 0 ≤ Cdown)
    (hC₀ : 1 < C₀) (hρ : 0 < ρ) (hζ : C₀ * ρ ^ 8 < 1)
    (k : ℕ) (x : ℕ → E) (j : Fin k) (p : E)
    (hsource : ‖p‖ ≤
      Cup * (∑ l ∈ Finset.univ.filter (fun l : Fin k => j < l),
        b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖) +
      Cdown * (∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j),
        b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖) +
      (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
        (β₀ * weightedFamilyNorm (C₀ * ρ ^ 6) k x + g)) :
    ‖p‖ ≤ (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
      ((β₀ + weightedInteractionRowFeedback b Cup Cdown C₀ ρ) *
        weightedFamilyNorm (C₀ * ρ ^ 6) k x + g) := by
  have hu := mul_le_mul_of_nonneg_left
    (weighted_inner_row_sum_bound hb hb1 hC₀ hρ k x j) hup
  have hd := mul_le_mul_of_nonneg_left
    (weighted_outer_row_sum_bound hb hb1 hC₀ hρ hζ k x j) hdown
  exact hsource.trans ((add_le_add (add_le_add hu hd) le_rfl).trans_eq (by
    unfold weightedInteractionRowFeedback
    ring))

theorem weighted_existing_trajectory_row_envelope
    {f : E → E} {U : Set E} {K b : ℝ≥0} (hLip : LipschitzOnWith K f U)
    (hb : 0 < b) (hb1 : b ≤ 1)
    {T Cup Cdown C₀ ρ β₀ : ℝ} (hT : 0 ≤ T) (hup : 0 ≤ Cup) (hdown : 0 ≤ Cdown)
    (hC₀ : 1 < C₀) (hρ : 0 < ρ) (hζ : C₀ * ρ ^ 8 < 1) (hβ₀ : 0 ≤ β₀)
    (k : ℕ) (a : ℕ → ℝ≥0) (ha : ∀ j : Fin k, a j ≤ b)
    (y c p : ℕ → ℝ → E) (g : ℝ → ℝ)
    (hgc : ContinuousOn g (Icc (0 : ℝ) T)) (hgn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ g t)
    (hyd : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (y j) ((a j : ℝ) • f (y j t) + p j t) t)
    (hcd : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (c j) ((a j : ℝ) • f (c j t)) t)
    (hym : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T, y j t ∈ U)
    (hcm : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T, c j t ∈ U)
    (hsource : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T, ‖p j t‖ ≤
      Cup * (∑ l ∈ Finset.univ.filter (fun l : Fin k => j < l),
        (b : ℝ) ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖y l t - c l t‖) +
      Cdown * (∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j),
        (b : ℝ) ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖y l t - c l t‖) +
      (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
        (β₀ * weightedFamilyNorm (C₀ * ρ ^ 6) k (fun i => y i t - c i t) + g t)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      weightedFamilyNorm (C₀ * ρ ^ 6) k (fun i => y i t - c i t) ≤
        weightedFamilyNorm (C₀ * ρ ^ 6) k (fun i => y i 0 - c i 0) *
          Real.exp ((((b * K : ℝ≥0) : ℝ) + β₀ +
            weightedInteractionRowFeedback b Cup Cdown C₀ ρ) * t) +
        ∫ s in (0)..t, Real.exp ((((b * K : ℝ≥0) : ℝ) + β₀ +
          weightedInteractionRowFeedback b Cup Cdown C₀ ρ) * (t - s)) * g s := by
  have hC : 0 < C₀ := by linarith
  have hh : 0 < C₀ * ρ ^ 6 := by positivity
  have hfeedback := weightedInteractionRowFeedback_nonneg b.coe_nonneg hup hdown hC₀ hζ
  have hfinal := weighted_existing_trajectory_integral_envelope hLip hh hT
    (add_nonneg hβ₀ hfeedback) k a ha y c p g hgc hgn hyd hcd hym hcm
    (fun j t ht => weighted_interaction_row_source_bound (show (0 : ℝ) < b from hb)
      (show (b : ℝ) ≤ 1 from hb1) hup hdown hC₀ hρ hζ k
      (fun i => y i t - c i t) j (p j t) (hsource j t ht))
  simpa only [add_assoc] using hfinal

end Euler2D

end
