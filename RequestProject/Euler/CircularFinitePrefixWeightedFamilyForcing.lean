module

public import RequestProject.Euler.CircularFinitePrefixWeightedForcing

/-! The complete actual weighted Little forcing for both material
interfaces, with the original Pi norm and no loss of constants. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)
theorem exists_uniform_actualPrefix_weighted_family_forcing :
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
      ∀ W : Fin 2 → LittleContourSpace η,
      (∀ i z, ‖ContourC1Space.toBCF η (W i).val z‖ ≤ B * radScale R ρ j) →
      (∀ i z, e * radScale R ρ j ≤ ‖ContourC1Space.toBCF η (W i).val z‖) →
      (∀ i, ‖W i‖ ≤ radScale R ρ j * L) →
      ∃ Q : Fin 2 → LittleContourSpace η,
        (∀ i θ, LittleContourSpace.lift η (Q i) θ =
          P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k
            (j.isLt.le.trans hkN) S t (LittleContourSpace.lift η (W i) θ)) ∧
        let Cu := finiteInnerLabelLittleRowCoefficient (η : ℝ) e L
        let Cl := finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L
        let CtR := Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
          (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
            ((CtR * b + weightedInteractionRowFeedback b (Cu + CtR) (Cl + CtR) C₀ ρ) *
              weightedFamilyNorm (C₀ * ρ ^ 6) k x + (Cu + CtR) / C₀ * ‖x k‖ +
              finitePrefixCompleteDeepBudget (η : ℝ) e L Cd Cb b R ρ D) := by
  obtain ⟨Ct, Cd, hCt, hCd, hsource⟩ := P.exists_uniform_actualPrefix_weighted_contourLittle_forcing
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro η hη s A₀ b R ρ c B δ e a L Cb D C₀ hs hA hb hb1 hR hRmax hρ hρ1 hsmall
    ha ha16 hc hB he hL hCb hD hC₀ hζ N k j hkN f T S hS t ht G x hq
    hsepU hsepL hradius hgeom hchart hsupp hsep W hWmax hWmin hWL
  classical
  have hex (i : Fin 2) := hsource hη hs hA hb hb1 hR hRmax hρ hρ1 hsmall
    ha ha16 hc hB he hL hCb hD hC₀ hζ N k j hkN S hS t ht G x hq
    hsepU hsepL hradius hgeom hchart hsupp hsep (W i) (hWmax i) (hWmin i) (hWL i)
  choose Qi hQi hn using hex
  refine ⟨Qi, hQi, ?_⟩
  let Cu := finiteInnerLabelLittleRowCoefficient (η : ℝ) e L
  let Cl := finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L
  let CtR := Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8
  let Budget := (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
    ((CtR * b + weightedInteractionRowFeedback b (Cu + CtR) (Cl + CtR) C₀ ρ) *
      weightedFamilyNorm (C₀ * ρ ^ 6) k x + (Cu + CtR) / C₀ * ‖x k‖ +
      finitePrefixCompleteDeepBudget (η : ℝ) e L Cd Cb b R ρ D)
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hden : 0 < ampScale A₀ b k * radScale R ρ j := mul_pos hAk (radScale_pos hR hρ j)
  have hBudget0 : 0 ≤ Budget :=
    (div_nonneg (norm_nonneg (Qi 0)) hden.le).trans (hn 0)
  change ‖Qi‖ / (ampScale A₀ b k * radScale R ρ j) ≤ Budget
  apply (div_le_iff₀ hden).mpr
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hBudget0 hden.le)).mpr
  intro i
  exact (div_le_iff₀ hden).mp (hn i)

end CircularMaterialTransferProfile
end Euler2D

end
