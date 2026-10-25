module

public import RequestProject.Euler.CircularFinitePrefixCompleteForcing
public import RequestProject.Euler.CurrentPrefixRowSums

/-! The current cell's complete genuine external field has the
capture polynomial budget and the periodic self term. All ancestor
labels are controlled by the existing weighted maximum; the field is
constructed from the same S, not supplied as a forcing assumption. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def finiteCurrentPolynomialForcingCoefficient (η e L Cb b Cd : ℝ) : ℝ :=
  (2 / b) * (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L +
    Cd * torusCorrectionContourBudget η L * finiteLabelMassBound) * Cb ^ 4

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCurrent_complete_forcing_budget :
    ∃ Ct Cd : ℝ, 0 < Ct ∧ 0 < Cd ∧ ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 →
      ∀ {s A₀ b R ρ c B δ e a L Cb D C₀ K Δ : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → b ≤ 1 → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 ≤ b / 2 →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 < B → 0 < e →
      0 ≤ L → 0 ≤ Cb → 0 ≤ D → 1 ≤ C₀ → 0 ≤ K → 0 ≤ Δ →
      C₀ * ρ ^ 8 ≤ 1 / 2 → 8 * B * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (2 * b * C₀ * K * (finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L +
        Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L)) * ρ ^ 2 ≤ Δ →
      ∀ (N k : ℕ) (hkN : k ≤ N),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S →
      ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ x : ℕ → Fin 2 → LittleContourSpace γ,
      weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ K →
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * ‖x l‖) →
      (L + 1) * radScale R ρ k ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + D) ≤ a →
      (∀ y ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖y - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t y = 0) →
      8 * (Cb * ρ * (1 + D)) ≤ e →
      ∀ W : LittleContourSpace η,
      (∀ z, ‖ContourC1Space.toBCF η W.val z‖ ≤ B * radScale R ρ k) →
      (∀ z, e * radScale R ρ k ≤ ‖ContourC1Space.toBCF η W.val z‖) →
      ‖W‖ ≤ radScale R ρ k * L →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N k k hkN S t (LittleContourSpace.lift η W θ)) ∧
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ k) ≤
          Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 * ‖x k‖ +
            (finiteCurrentPolynomialForcingCoefficient (η : ℝ) e L Cb b Cd + Δ) *
              ρ ^ 6 * (1 + D) ^ 4 := by
  obtain ⟨Ct, Cd, hCt, hCd, hcomplete⟩ := P.exists_uniform_finitePrefix_complete_contourLittle_rows
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro η hη s A₀ b R ρ c B δ e a L Cb D C₀ K Δ hs hA hb hb1 hR hRmax hρ hρ1 hhalf
    ha ha16 hc hB he hL hCb hD hC₀ hK hΔ hζ hsepL hRchart hsmall
    N k hkN f T S hS t ht G x hx hq hgeom hchart hsupp hsep W hWmax hWmin hWL
  have hρsmall : ρ ^ 2 < b := by linarith
  have hC₀pos : 0 < C₀ := by linarith
  have hR1 : R ≤ 1 := by linarith
  have hR8 : R ^ 8 ≤ 1 := pow_le_one₀ hR.le hR1
  have hr (l : ℕ) : 0 < radScale R ρ l := radScale_pos hR hρ l
  have hsepL' (l : Fin (k + 1)) (hl : (l : ℕ) < k) :
      8 * (B * radScale R ρ k) ≤ c * radScale R ρ l := by
    have hh := radScale_le_ratio_of_lt hR hρ hρ1 hl
    calc
      _ = (8 * B) * radScale R ρ k := by ring
      _ ≤ (8 * B) * (ρ * radScale R ρ l) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := by convert mul_le_mul_of_nonneg_right hsepL (hr l).le using 1 <;> ring
  have hrad (l : Fin (k + 1)) : (5 / 4 : ℝ) * radScale R ρ l ≤ a :=
    (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)) (by norm_num : (0 : ℝ) ≤ 5 / 4)).trans hRchart
  have hsep' : 8 * (Cb * ρ * radScale R ρ k * (1 + D)) ≤ e * radScale R ρ k := by
    convert mul_le_mul_of_nonneg_right hsep (hr k).le using 1 <;> ring
  obtain ⟨Q, hQ, hn⟩ := hcomplete hη hs hA hb hR hRmax hρ hρ1 hρsmall ha ha16 hc hB he
    hL hCb hD hC₀ N k k hkN le_rfl S hS t ht G (fun l => ‖x l‖)
    (fun _ => norm_nonneg _) hq
    (fun l hl => by have hh := l.isLt; omega) hsepL' hrad hgeom hchart hsupp hsep' W hWmax hWmin hWL
  let O := finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L
  let U := finiteInnerLabelLittleRowCoefficient (η : ℝ) e L
  let V := Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hInt : 0 ≤ interiorContourNormBudget (η : ℝ) 1 c B L :=
    (interiorSpatialDerivativeBudget_nonneg (by norm_num : (0 : ℝ) ≤ 1) hB 0).trans (le_max_left _ _)
  have hO : 0 ≤ O := by unfold O finiteOuterLabelLittleRowCoefficient; positivity
  have hV : 0 ≤ V := mul_nonneg hCt.le (finiteTorusLabelLittleRowCoefficient_nonneg hL)
  have hrows := current_prefix_rows_le_polynomial_margin (U := U) hO hV hR8 hb
    hb1 hC₀pos hρ hζ hK hΔ k x hx hsmall hD
  have hCauchy : 0 ≤ cauchyContourNormBudget 5 (η : ℝ) 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have hTor : 0 ≤ torusCorrectionContourBudget (η : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hden : 0 < b * (1 - ρ ^ 2 / b) := mul_pos hb (sub_pos.mpr ((div_lt_one hb).mpr hρsmall))
  have hdenHalf : b / 2 ≤ b * (1 - ρ ^ 2 / b) := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hb.ne']
    linarith
  let J := finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L
  let Jt := Cd * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound
  have hJ : 0 ≤ J := mul_nonneg finiteLabelMassBound_nonneg hCauchy
  have hJt : 0 ≤ Jt := by unfold Jt; positivity [finiteLabelMassBound_nonneg]
  have hdeep :
      ((finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) *
        Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b))) +
      (Cd * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound *
        Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b))) ≤
      finiteCurrentPolynomialForcingCoefficient (η : ℝ) e L Cb b Cd * ρ ^ 6 * (1 + D) ^ 4 := by
    calc
      _ = ((J + Jt * R ^ 8) * Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4) / (b * (1 - ρ ^ 2 / b)) := by
        unfold J Jt
        ring
      _ ≤ ((J + Jt) * Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4) / (b * (1 - ρ ^ 2 / b)) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_of_le_one_right hJt hR8) J) (by positivity))
            (by positivity)) (by positivity)
      _ ≤ ((J + Jt) * Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4) / (b / 2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hb) hdenHalf
      _ = _ := by unfold J Jt finiteCurrentPolynomialForcingCoefficient; ring
  simp only [Nat.sub_self, pow_zero, one_mul] at hn
  refine ⟨Q, hQ, ?_⟩
  have hh := hn.trans (add_le_add hrows hdeep)
  exact hh.trans_eq (by unfold V; ring)

end CircularMaterialTransferProfile
end Euler2D

end
