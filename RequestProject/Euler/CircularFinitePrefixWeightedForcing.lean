module

public import RequestProject.Euler.CircularFinitePrefixCompleteForcing
public import RequestProject.Euler.CompleteWeightedInteractionRows

/-! The complete same-S forcing, now in the finite weighted ancestor
norm. The current source and true rough deep cluster stay explicit. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def finitePrefixCompleteDeepBudget (η e L Cd Cb b R ρ D : ℝ) : ℝ :=
  ((finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) *
    Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b))) +
  (Cd * torusCorrectionContourBudget η L * finiteLabelMassBound *
    Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)))

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualPrefix_weighted_contourLittle_forcing :
    ∃ Ct Cd : ℝ, 0 < Ct ∧ 0 < Cd ∧ ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 →
      ∀ {s A₀ b R ρ c B δ e a L Cb D C₀ : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → b ≤ 1 → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 < b →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 < B → 0 < e →
      0 ≤ L → 0 ≤ Cb → 0 ≤ D → 1 < C₀ → C₀ * ρ ^ 8 < 1 →
      ∀ (N k : ℕ) (j : Fin k) (hkN : k ≤ N),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S →
      ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ x : ℕ → Fin 2 → LittleContourSpace η,
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * ‖x l‖) →
      (∀ l : Fin (k + 1), (j : ℕ) < l → 10 * radScale R ρ l ≤ e * radScale R ρ j) →
      (∀ l : Fin (k + 1), (l : ℕ) < j → 8 * (B * radScale R ρ j) ≤ c * radScale R ρ l) →
      (∀ l : Fin (k + 1), (5 / 4 : ℝ) * radScale R ρ l ≤ a) →
      (L + 1) * radScale R ρ j ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + D) ≤ a →
      (∀ z ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖z - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t z = 0) →
      8 * (Cb * ρ * radScale R ρ k * (1 + D)) ≤ e * radScale R ρ j →
      ∀ W : LittleContourSpace η,
      (∀ z, ‖ContourC1Space.toBCF η W.val z‖ ≤ B * radScale R ρ j) →
      (∀ z, e * radScale R ρ j ≤ ‖ContourC1Space.toBCF η W.val z‖) →
      ‖W‖ ≤ radScale R ρ j * L →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k
            (j.isLt.le.trans hkN) S t (LittleContourSpace.lift η W θ)) ∧
        let Cu := finiteInnerLabelLittleRowCoefficient (η : ℝ) e L
        let Cl := finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L
        let CtR := Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
          (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
            ((CtR * b + weightedInteractionRowFeedback b (Cu + CtR) (Cl + CtR) C₀ ρ) *
              weightedFamilyNorm (C₀ * ρ ^ 6) k x + (Cu + CtR) / C₀ * ‖x k‖ +
              finitePrefixCompleteDeepBudget (η : ℝ) e L Cd Cb b R ρ D) := by
  obtain ⟨Ct, Cd, hCt, hCd, hsource⟩ := P.exists_uniform_finitePrefix_complete_contourLittle_rows
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro η hη s A₀ b R ρ c B δ e a L Cb D C₀ hs hA hb hb1 hR hRmax hρ hρ1 hsmall
    ha ha16 hc hB he hL hCb hD hC₀ hζ N k j hkN f T S hS t ht G x hq
    hsepU hsepL hradius hgeom hchart hsupp hsep W hWmax hWmin hWL
  obtain ⟨Q, hQ, hn⟩ := hsource hη hs hA hb hR hRmax hρ hρ1 hsmall
    ha ha16 hc hB he hL hCb hD hC₀.le N k j hkN j.isLt.le S hS t ht G
    (fun l => ‖x l‖) (fun _ => norm_nonneg _) hq hsepU hsepL hradius hgeom hchart hsupp hsep W hWmax hWmin hWL
  let Cu := finiteInnerLabelLittleRowCoefficient (η : ℝ) e L
  let Cl := finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L
  let CtR := Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hshapeu : 0 ≤ cauchyContourNormBudget 5 (η : ℝ) 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have hshapel : 0 ≤ interiorContourNormBudget (η : ℝ) 1 c B L :=
    (interiorSpatialDerivativeBudget_nonneg (M := 1) (a := c) (by norm_num) hB 0).trans (le_max_left _ _)
  have hCu : 0 ≤ Cu := by unfold Cu finiteInnerLabelLittleRowCoefficient; positivity
  have hCl : 0 ≤ Cl := by unfold Cl finiteOuterLabelLittleRowCoefficient; positivity
  have hCtcoef : 0 ≤ finiteTorusLabelLittleRowCoefficient (η : ℝ) L :=
    finiteTorusLabelLittleRowCoefficient_nonneg hL
  have hCtR : 0 ≤ CtR := by unfold CtR; positivity
  have hn' : ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
      completeInteractionRowSum Cu Cl CtR b ρ k j x +
        (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * finitePrefixCompleteDeepBudget (η : ℝ) e L Cd Cb b R ρ D := hn
  have hrows := completeInteractionRowSum_weighted_bound hCu hCl hCtR hb hb1 hρ hC₀ hζ k j x
  refine ⟨Q, hQ, ?_⟩
  exact hn'.trans ((add_le_add hrows le_rfl).trans_eq (by ring))

end CircularMaterialTransferProfile
end Euler2D

end
