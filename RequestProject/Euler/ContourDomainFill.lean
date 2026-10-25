module

public import RequestProject.Euler.ContourEnclosedDomain

/-! An intrinsic radial-fill description of the actual enclosed domain,
and its genuine fourfold invariance when the original loop has it. -/

@[expose] public section

noncomputable section

open Complex Set

namespace Euler2D

def contourRadialFill (z : ℝ → ℂ) : Set ℂ :=
  {x | ∃ θ t : ℝ, 0 ≤ t ∧ t < 1 ∧ x = t • z θ}

theorem contourRadialFill_eq_of_range_eq {z w : ℝ → ℂ} (h : Set.range z = Set.range w) :
    contourRadialFill z = contourRadialFill w := by
  apply Set.Subset.antisymm
  · rintro x ⟨θ, t, ht0, ht1, rfl⟩
    obtain ⟨φ, hφ⟩ := h ▸ (Set.mem_range_self θ : z θ ∈ Set.range z)
    exact ⟨φ, t, ht0, ht1, congrArg (fun y : ℂ => t • y) hφ.symm⟩
  · rintro x ⟨φ, t, ht0, ht1, rfl⟩
    obtain ⟨θ, hθ⟩ := h.symm ▸ (Set.mem_range_self φ : w φ ∈ Set.range w)
    exact ⟨θ, t, ht0, ht1, congrArg (fun y : ℂ => t • y) hθ.symm⟩

theorem starDomain_eq_contourRadialFill {R : ℝ → ℝ} {a : ℝ}
    (hR : Continuous R) (hp : Function.Periodic R (2 * Real.pi))
    (ha : 0 < a) (hlo : ∀ θ, a ≤ R θ) :
    starDomain R = contourRadialFill (fun θ => (R θ : ℂ) * exp ((θ : ℂ) * I)) := by
  have hpos (θ : ℝ) : 0 < R θ := ha.trans_le (hlo θ)
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨arg x, ‖x‖ / R (arg x), div_nonneg (norm_nonneg _) (hpos _).le,
      (div_lt_one (hpos _)).mpr hx, ?_⟩
    dsimp only
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      div_mul_cancel₀ _ (hpos _).ne', Complex.norm_mul_exp_arg_mul_I]
  · rintro x ⟨θ, t, ht0, ht1, rfl⟩
    rw [starDomain_eq_gauge_lt_one hpos]
    change starDomainGauge R (t • ((R θ : ℂ) * exp ((θ : ℂ) * I))) < 1
    rw [starDomainGauge_real_smul ht0]
    have hb : starDomainGauge R ((R θ : ℂ) * exp ((θ : ℂ) * I)) = 1 := by
      have hm : (R θ : ℂ) * exp ((θ : ℂ) * I) ∈ frontier (starDomain R) := by
        rw [frontier_starDomain_eq_range hR hp ha hlo]
        exact Set.mem_range_self θ
      rw [frontier_starDomain hR hp ha hlo] at hm
      exact hm
    rw [hb, mul_one]
    exact ht1

theorem nearCircleEnclosedDomain_eq_contourRadialFill {z dz : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)
    (hp : Function.Periodic z (2 * Real.pi)) :
    nearCircleEnclosedDomain hr hε hsmall hz hv hd = contourRadialFill z := by
  change starDomain _ = _
  rw [starDomain_eq_contourRadialFill
    (continuous_nearCircleRadialProfile hr hε hsmall hz hv hd)
    (periodic_nearCircleRadialProfile hr hε hsmall hz hv hd hp)
    (show 0 < r - ε by linarith)
    (fun φ => (nearCircleRadialProfile_bounds hr hε hsmall hz hv hd φ).1)]
  exact contourRadialFill_eq_of_range_eq (nearCircleRadialGraph_range hr hε hsmall hz hv hd)

theorem mul_I_mem_contourRadialFill {z : ℝ → ℂ}
    (hrot : ∀ θ, z (θ + Real.pi / 2) = I * z θ)
    {x : ℂ} (hx : x ∈ contourRadialFill z) : I * x ∈ contourRadialFill z := by
  obtain ⟨θ, t, ht0, ht1, rfl⟩ := hx
  refine ⟨θ + Real.pi / 2, t, ht0, ht1, ?_⟩
  rw [hrot]
  simp only [Complex.real_smul]
  ring

theorem mul_I_mem_contourRadialFill_iff {z : ℝ → ℂ}
    (hrot : ∀ θ, z (θ + Real.pi / 2) = I * z θ) (x : ℂ) :
    I * x ∈ contourRadialFill z ↔ x ∈ contourRadialFill z := by
  constructor
  · intro hx
    have h := mul_I_mem_contourRadialFill hrot
      (mul_I_mem_contourRadialFill hrot (mul_I_mem_contourRadialFill hrot hx))
    simpa [← mul_assoc] using h
  · exact mul_I_mem_contourRadialFill hrot

end Euler2D
