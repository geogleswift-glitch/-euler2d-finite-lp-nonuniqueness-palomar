module

public import RequestProject.Euler.CircularFiniteRealRadialFeedback

/-! The actual same-S ancestor residuals, after their circular
references are subtracted, give the weighted ancestor forcing in the
original Little norm. No prescribed forcing or error equation is used. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def finiteAncestorIndex {N k : ℕ} (hk : k ≤ N) (j : Fin k) : Fin (N + 1) :=
  ⟨j, j.isLt.trans_le (hk.trans (Nat.le_succ N))⟩

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteAncestorResidual_contourLittle_weighted
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c B L : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (hc : 0 < c) (hB : 0 < B)
    (q : Fin k → ℝ)
    (G : ∀ j : Fin k, P.FiniteOuterMaterialTube s R ρ N j S t c (q j))
    (hsep : 8 * B * ρ ≤ c)
    (W : LittleContourSpace η)
    (hW : ∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * radScale R ρ k)
    (hL : ‖W‖ ≤ radScale R ρ k * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        ∑ j : Fin k, velocityC
          (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (finiteAncestorIndex hk j) S t)
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / (ampScale A₀ b k * radScale R ρ k) ≤
        (interiorContourNormBudget (η : ℝ) 1 c B L *
          (4 * Real.pi * circularRadialPerturbationWeight)) *
          ∑ j : Fin k, (b * ρ ^ 2) ^ (k - (j : ℕ)) * q j := by
  have hrk : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hex : ∀ j : Fin k, ∃ Qj : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Qj θ =
        velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (finiteAncestorIndex hk j) S t)
          (LittleContourSpace.lift η W θ)) ∧
      ‖Qj‖ / (ampScale A₀ b k * radScale R ρ k) ≤
        (interiorContourNormBudget (η : ℝ) 1 c B L * (4 * Real.pi * circularRadialPerturbationWeight)) *
          (b * ρ ^ 2) ^ (k - (j : ℕ)) * q j := by
    intro j
    let jj := finiteAncestorIndex hk j
    have hjj : (jj : ℕ) ≤ (j : ℕ) := le_rfl
    have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
    have hAj : 0 < ampScale A₀ b j := by unfold ampScale; positivity
    have hrkj : radScale R ρ k ≤ ρ * radScale R ρ j := by
      calc
        _ ≤ R * ρ ^ ((j : ℕ) + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ1 (Nat.succ_le_of_lt j.isLt)) hR.le
        _ = _ := by simp only [radScale, pow_succ]; ring
    have hsepr : 8 * (B * radScale R ρ k) ≤ c * radScale R ρ jj := by
      calc
        _ ≤ 8 * (B * (ρ * radScale R ρ j)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrkj hB.le) (by norm_num)
        _ = (8 * B * ρ) * radScale R ρ j := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsep hrj.le
    obtain ⟨Qj, hQj, hn⟩ := P.exists_finiteOuterLabel_contourLittle_ratio hs hR hRmax hρ hρ1
      N jj S (G j).contours t ht ((G j).initial_box jj hjj) ((G j).current_box jj hjj)
      ((G j).images jj hjj) hη (fun i => (G j).reference (jj, i)) (fun i => (G j).shifts (jj, i))
      hc hB hrk ((G j).reference_lift jj hjj) ((G j).quarter_tube jj hjj)
      ((G j).relative_tube jj hjj) (G j).core ((G j).fourfold jj hjj) hsepr W hW hL
    rw [finiteCircularInterfaceRadialWeight_eq,
      abs_of_nonneg (show 0 ≤ ampScale A₀ b jj from hAj.le)] at hn
    have hn' := div_le_div_of_nonneg_right hn hAk.le
    have heq :
        (interiorContourNormBudget (η : ℝ) 1 c B L *
          (4 * Real.pi * (ampScale A₀ b jj * circularRadialPerturbationWeight)) *
            (radScale R ρ k / radScale R ρ jj) ^ 2 * q j) / ampScale A₀ b k =
        (interiorContourNormBudget (η : ℝ) 1 c B L * (4 * Real.pi * circularRadialPerturbationWeight)) *
          ((ampScale A₀ b jj * (radScale R ρ k / radScale R ρ jj) ^ 2) / ampScale A₀ b k) * q j := by ring
    rw [heq, outer_contour_scale_identity (j := (jj : ℕ)) hA hb hR hρ (Nat.le_of_lt j.isLt)] at hn'
    refine ⟨Qj, hQj, ?_⟩
    simpa only [div_div, mul_comm] using hn'
  choose Qj hQj hn using hex
  refine ⟨∑ j, Qj j, ?_, ?_⟩
  · intro θ
    change LittleContourSpace.eval η (θ : ContourCircle) (∑ j, Qj j) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => hQj j θ)
  · calc
      _ ≤ (∑ j, ‖Qj j‖) / (ampScale A₀ b k * radScale R ρ k) :=
        div_le_div_of_nonneg_right (norm_sum_le _ _) (mul_pos hAk hrk).le
      _ = ∑ j, ‖Qj j‖ / (ampScale A₀ b k * radScale R ρ k) := Finset.sum_div _ _ _
      _ ≤ ∑ j : Fin k,
          (interiorContourNormBudget (η : ℝ) 1 c B L * (4 * Real.pi * circularRadialPerturbationWeight)) *
            (b * ρ ^ 2) ^ (k - (j : ℕ)) * q j := Finset.sum_le_sum (fun j _ => hn j)
      _ = _ := by simp only [Finset.mul_sum, mul_assoc]

end CircularMaterialTransferProfile
end Euler2D

end
