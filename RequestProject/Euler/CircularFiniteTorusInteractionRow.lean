module

public import RequestProject.Euler.CircularFiniteTorusLabelPerturbation
public import RequestProject.Euler.CircularTorusInteractionScale

/-! Both current-clock rows for the actual periodic velocity of one
original transported label. The same constructed Little field has
the upper or lower interaction coefficient according to source order,
with the original R^8 factor and that source's own deviation. -/

@[expose] public section

set_option maxHeartbeats 4500000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def finiteTorusLabelLittleRowCoefficient (η L : ℝ) : ℝ :=
  torusCorrectionContourBudget η L * (4 * Real.pi * circularRadialPerturbationWeight) *
    (5 / 4 : ℝ) ^ 4

theorem finiteTorusLabelLittleRowCoefficient_nonneg {η L : ℝ} (hL : 0 ≤ L) :
    0 ≤ finiteTorusLabelLittleRowCoefficient η L := by
  have hB : 0 ≤ torusCorrectionContourBudget η L := by
    unfold torusCorrectionContourBudget
    positivity
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  unfold finiteTorusLabelLittleRowCoefficient
  positivity

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_finiteLabel_torus_contourLittle_rows :
    ∃ C : ℝ, 0 < C ∧ ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 →
      ∀ {s A₀ b R ρ c δ ql a L : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → 0 < a → a ≤ 1 / 16 →
      ∀ (N k j : ℕ) (l : Fin (N + 1)), (l : ℕ) ≤ k →
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N l S t c δ,
      0 ≤ ql →
      (∀ i, ‖contourParameterShiftC1 (G.shifts (l, i)) (G.contours (l, i)) -
        G.reference (l, i)‖ ≤ radScale R ρ l * ql) →
      (5 / 4 : ℝ) * radScale R ρ l ≤ a →
      0 ≤ L → (L + 1) * radScale R ρ j ≤ a / 2 →
      ∀ W : LittleContourSpace η, ‖W‖ ≤ L * radScale R ρ j →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          actualTorusCorrectionVelocity
            (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t))
            (LittleContourSpace.lift η W θ)) ∧
        (j ≤ (l : ℕ) → ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
          C * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 *
            b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ql) ∧
        ((l : ℕ) ≤ j → ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
          C * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 *
            b ^ (k - (l : ℕ)) * ρ ^ (2 * (j - (l : ℕ))) * ql) := by
  obtain ⟨C, hC, hsource⟩ := P.exists_uniform_finiteLabel_torus_contourLittle_perturbation
  refine ⟨C, hC, ?_⟩
  intro η hη s A₀ b R ρ c δ ql a L hs hA hb hR hRmax hρ hρ1 ha ha16
    N k j l hlk f T S t ht G hql0 hql hradius hL hgeom W hW
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  obtain ⟨Q, hQ, hn⟩ := hsource hη hs hA hb hR hRmax hρ hρ1 ha ha16 N l S t ht G
    hql0 hql hradius (radScale_pos hR hρ j) hL hgeom W hW
  have hcoef : 0 ≤ C * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * ql :=
    mul_nonneg (mul_nonneg hC.le (finiteTorusLabelLittleRowCoefficient_nonneg hL)) hql0
  have hbase : ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
      (C * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * ql) *
        ((ampScale A₀ b l * radScale R ρ j ^ 2 * radScale R ρ l ^ 6) / ampScale A₀ b k) := by
    calc
      _ = (‖Q‖ / radScale R ρ j) / ampScale A₀ b k := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hn hAk.le
      _ = _ := by unfold finiteTorusLabelLittleRowCoefficient; ring
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro hjl
    exact (hbase.trans (mul_le_mul_of_nonneg_left
      (torus_inner_current_clock_le hA.ne' hb hR hρ hρ1 hjl hlk) hcoef)).trans_eq (by ring)
  · intro hlj
    exact (hbase.trans (mul_le_mul_of_nonneg_left
      (torus_outer_current_clock_le hA.ne' hb hR hρ hρ1 hlj hlk) hcoef)).trans_eq (by ring)

end CircularMaterialTransferProfile
end Euler2D

end
