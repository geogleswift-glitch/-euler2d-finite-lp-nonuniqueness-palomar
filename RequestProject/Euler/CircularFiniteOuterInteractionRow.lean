module

public import RequestProject.Euler.CircularFiniteInnerInteractionRow

/-! The actual ancestor residual has the original lower-row scale in
the same current k clock. Only the source label's own displacement
enters; no shared weighted bound on earlier labels is assumed. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem outer_contour_current_clock_identity {A₀ b R ρ : ℝ}
    (hA : A₀ ≠ 0) (hb : b ≠ 0) (hR : R ≠ 0) (hρ : ρ ≠ 0)
    {l j k : ℕ} (hlj : l ≤ j) (hlk : l ≤ k) :
    (ampScale A₀ b l * (radScale R ρ j / radScale R ρ l) ^ 2) / ampScale A₀ b k =
      b ^ (k - l) * ρ ^ (2 * (j - l)) := by
  calc
    _ = (ampScale A₀ b l / ampScale A₀ b k) * (radScale R ρ j / radScale R ρ l) ^ 2 := by ring
    _ = _ := by rw [ampScale_ratio_eq_pow hA hb hlk, radScale_ratio_eq_pow hR hρ hlj, ← pow_mul, Nat.mul_comm]

def finiteOuterLabelLittleRowCoefficient (η c B L : ℝ) : ℝ :=
  interiorContourNormBudget η 1 c B L * (4 * Real.pi * circularRadialPerturbationWeight)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteOuterLabel_contourLittle_lowerRow
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c B δ ql L : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k j : ℕ) (l : Fin (N + 1)) (hlj : (l : ℕ) ≤ j) (hlk : (l : ℕ) ≤ k)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N l S t c δ)
    (hql : ∀ i, ‖contourParameterShiftC1 (G.shifts (l, i)) (G.contours (l, i)) -
      G.reference (l, i)‖ ≤ radScale R ρ l * ql)
    (hc : 0 < c) (hB : 0 < B)
    (hsep : 8 * (B * radScale R ρ j) ≤ c * radScale R ρ l)
    (W : LittleContourSpace η)
    (hW : ∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * radScale R ρ j)
    (hL : ‖W‖ ≤ radScale R ρ j * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N l S t)
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
        finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L * b ^ (k - (l : ℕ)) *
          ρ ^ (2 * (j - (l : ℕ))) * ql := by
  have hAl : 0 < ampScale A₀ b l := by unfold ampScale; positivity
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  obtain ⟨Q, hQ, hn⟩ := P.exists_finiteOuterLabel_contourLittle_ratio hs hR hRmax hρ hρ1
    N l S G.contours t ht (G.initial_box l le_rfl) (G.current_box l le_rfl) (G.images l le_rfl)
    hη (fun i => G.reference (l, i)) (fun i => G.shifts (l, i))
    hc hB (radScale_pos hR hρ j) (G.reference_lift l le_rfl) (G.quarter_tube l le_rfl)
    hql G.core (G.fourfold l le_rfl) hsep W hW hL
  rw [finiteCircularInterfaceRadialWeight_eq, abs_of_nonneg hAl.le] at hn
  refine ⟨Q, hQ, ?_⟩
  have hn' := div_le_div_of_nonneg_right hn hAk.le
  calc
    _ = (‖Q‖ / radScale R ρ j) / ampScale A₀ b k := by ring
    _ ≤ _ := hn'
    _ = finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L *
        ((ampScale A₀ b l * (radScale R ρ j / radScale R ρ l) ^ 2) / ampScale A₀ b k) * ql := by
      unfold finiteOuterLabelLittleRowCoefficient
      ring
    _ = _ := by rw [outer_contour_current_clock_identity hA.ne' hb.ne' hR.ne' hρ.ne' hlj hlk]; ring

end CircularMaterialTransferProfile
end Euler2D

end
