module

public import RequestProject.Euler.CircularOuterScaleAlgebra
public import RequestProject.Euler.CircularFiniteOuterRadialFeedback

/-! The full actual finite planar field has a uniform radial feedback
bound derived from all actual outer material tubes and the genuine
inner-cluster self-speed. Constants precede every finite scale. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_physicalFiniteDensity_planarRadial_feedback :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ : ℝ}, s ≤ 0 → 0 ≤ A₀ → 0 < b →
      0 < R → R ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 → ρ < b → b * ρ ^ 2 < 1 →
      ∀ N k : ℕ, k ≤ N → ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
        (Z Z₀ : FiniteCircularIndex N → ContourC1Space γ) (β : FiniteCircularIndex N → ℝ)
        {t c δ : ℝ}, t ∈ Icc (0 : ℝ) T → 0 < c → 0 ≤ δ →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i, ContourC1Space.lift γ (Z₀ (j, i)) =
        refCircle (circularContourRadii i * radScale R ρ j)) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
        ‖contourParameterShiftC1 (β (j, i)) (Z (j, i)) - Z₀ (j, i)‖ ≤
          circularContourRadii i * radScale R ρ j / 4) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
        ‖contourParameterShiftC1 (β (j, i)) (Z (j, i)) - Z₀ (j, i)‖ ≤ radScale R ρ j * δ) →
      (∀ i, c ≤ 3 * circularContourRadii i / 4) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i θ,
        ContourC1Space.lift γ (Z (j, i)) (θ + Real.pi / 2) = I * ContourC1Space.lift γ (Z (j, i)) θ) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) ⊆ torusBox) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z (j, i))) ⊆ torusBox) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill
          (ContourC1Space.lift γ (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z (j, i)))) →
      ∀ x : ℂ, ‖x‖ ≤ c * radScale R ρ k / 2 →
      (velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x * conj x).re ≤
        ‖x‖ * (C * ampScale A₀ b k * radScale R ρ k * (ρ / b) / (1 - ρ / b) +
          ((32 / (15 * c ^ 4) * circularRadialPerturbationWeight) * δ *
            (ampScale A₀ b k / radScale R ρ k ^ 2) / (1 - b * ρ ^ 2)) * ‖x‖ ^ 3) := by
  obtain ⟨C, hC, hinner⟩ := P.exists_uniform_finiteInnerCluster_planarVelocity_bound
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ hs hA hb hR hRmax hρ hρ1 hρb hsmall N k hk f T S Z Z₀ β t c δ ht hc hδ
    href hsmallTube hq hcore hrot hstartbox hendbox himages x hx
  let D : ℝ := 32 / (15 * c ^ 4) * circularRadialPerturbationWeight
  have hD : 0 ≤ D := by
    unfold D circularRadialPerturbationWeight
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hlabel (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      |(velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x * conj x).re| ≤
          (D * δ * ‖x‖ ^ 4) * (ampScale A₀ b j / radScale R ρ j ^ 2) := by
    have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    let ℓ : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le (hjk.trans hk)⟩
    have hℓ : (ℓ : ℕ) ≤ k := hjk
    have hrad : radScale R ρ k ≤ radScale R ρ j := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
      unfold radScale
      rw [pow_add]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg hρ.le j) (pow_le_one₀ hρ.le hρ1)) hR.le
    have hxl : ‖x‖ ≤ c * radScale R ρ ℓ / 2 := hx.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrad hc.le) (by norm_num))
    have hbnd := P.abs_radial_component_boxed_finitePeriodicLabel_le (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 N ℓ S Z t ht
      (hstartbox ℓ hℓ) (hendbox ℓ hℓ) (himages ℓ hℓ) (fun i => Z₀ (ℓ, i)) (fun i => β (ℓ, i)) hc
      (href ℓ hℓ) (hsmallTube ℓ hℓ) (hq ℓ hℓ) hcore (hrot ℓ hℓ) hxl
    have hAj : 0 ≤ ampScale A₀ b j := by unfold ampScale; positivity
    simpa only [ℓ, Fin.val_mk, abs_of_nonneg hAj, D, mul_div_assoc, div_mul_eq_mul_div,
      mul_assoc, mul_left_comm, mul_comm] using hbnd
  have houter : (∑ j ∈ Finset.range (k + 1), |(velocityC (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x * conj x).re|) ≤
        (D * δ * ‖x‖ ^ 4) * ((ampScale A₀ b k / radScale R ρ k ^ 2) / (1 - b * ρ ^ 2)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1),
          (D * δ * ‖x‖ ^ 4) * (ampScale A₀ b j / radScale R ρ j ^ 2) := Finset.sum_le_sum hlabel
      _ = (D * δ * ‖x‖ ^ 4) *
          ∑ j ∈ Finset.range (k + 1), ampScale A₀ b j / radScale R ρ j ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_outer_radial_scales_le hA hb hR hρ hsmall k) (by positivity)
  have hi := hinner hs hA hb hR hRmax hρ hρ1 hρb N k S t x
  exact (P.radial_component_physicalFiniteDensity_le_outer_add_cluster hs hA hb hR hRmax hρ hρ1
    N k hk S t x).trans ((add_le_add houter (mul_le_mul_of_nonneg_right hi (norm_nonneg _))).trans_eq (by
      dsimp [D]
      ring))

end CircularMaterialTransferProfile
end Euler2D

end
