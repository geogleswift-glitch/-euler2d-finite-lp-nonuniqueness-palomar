module

public import RequestProject.Euler.CircularFiniteInnerLabelPerturbationForcing
public import RequestProject.Euler.CircularAncestorTimeRescaling

/-! The real same-S label interaction has the original upper-row
coefficient b^(k-l)*rho^(6*(l-j)), in the unchanged current k clock. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem radScale_ratio_eq_pow {R ρ : ℝ} (hR : R ≠ 0) (hρ : ρ ≠ 0)
    {j l : ℕ} (hjl : j ≤ l) : radScale R ρ l / radScale R ρ j = ρ ^ (l - j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjl
  simp only [radScale, pow_add, Nat.add_sub_cancel_left]
  field_simp

theorem inner_contour_current_clock_identity {A₀ b R ρ : ℝ}
    (hA : A₀ ≠ 0) (hb : b ≠ 0) (hR : R ≠ 0) (hρ : ρ ≠ 0)
    {j l k : ℕ} (hjl : j ≤ l) (hlk : l ≤ k) :
    (ampScale A₀ b l * (radScale R ρ l / radScale R ρ j) ^ 6) / ampScale A₀ b k =
      b ^ (k - l) * ρ ^ (6 * (l - j)) := by
  calc
    _ = (ampScale A₀ b l / ampScale A₀ b k) * (radScale R ρ l / radScale R ρ j) ^ 6 := by ring
    _ = _ := by rw [ampScale_ratio_eq_pow hA hb hlk, radScale_ratio_eq_pow hR hρ hjl, ← pow_mul, Nat.mul_comm]

def finiteInnerLabelLittleRowCoefficient (η e L : ℝ) : ℝ :=
  cauchyContourNormBudget 5 η 1 e L * (4 * Real.pi * circularRadialPerturbationWeight) * (5 / 4 : ℝ) ^ 4

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteInnerLabel_contourLittle_upperRow
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c δ ql e L : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k j : ℕ) (l : Fin (N + 1)) (hjl : j ≤ (l : ℕ)) (hlk : (l : ℕ) ≤ k)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N l S t c δ)
    (hql0 : 0 ≤ ql)
    (hql : ∀ i, ‖contourParameterShiftC1 (G.shifts (l, i)) (G.contours (l, i)) -
      G.reference (l, i)‖ ≤ radScale R ρ l * ql)
    (he : 0 < e) (hsep : 10 * radScale R ρ l ≤ e * radScale R ρ j)
    (W : LittleContourSpace η)
    (hW : ∀ x, e * radScale R ρ j ≤ ‖ContourC1Space.toBCF η W.val x‖)
    (hL : ‖W‖ ≤ radScale R ρ j * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t))
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
        finiteInnerLabelLittleRowCoefficient (η : ℝ) e L * b ^ (k - (l : ℕ)) *
          ρ ^ (6 * ((l : ℕ) - j)) * ql := by
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  obtain ⟨Q, hQ, hn⟩ := P.exists_finiteInnerLabel_contourLittle_sixthRatio hη hs hA hb hR hRmax
    hρ hρ1 N l S t ht G hql0 hql he (radScale_pos hR hρ j) hsep W hW hL
  refine ⟨Q, hQ, ?_⟩
  have hn' := div_le_div_of_nonneg_right hn hAk.le
  calc
    _ = (‖Q‖ / radScale R ρ j) / ampScale A₀ b k := by ring
    _ ≤ _ := hn'
    _ = finiteInnerLabelLittleRowCoefficient (η : ℝ) e L *
        ((ampScale A₀ b l * (radScale R ρ l / radScale R ρ j) ^ 6) / ampScale A₀ b k) * ql := by
      unfold finiteInnerLabelLittleRowCoefficient
      ring
    _ = _ := by rw [inner_contour_current_clock_identity hA.ne' hb.ne' hR.ne' hρ.ne' hjl hlk]; ring

end CircularMaterialTransferProfile
end Euler2D

end
