module

public import RequestProject.Euler.CircularFiniteCurrentForcingBudget

/-! Both current material interfaces carry the same genuine forcing
budget in the original Pi norm. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCurrent_family_forcing_budget :
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
      ∀ W : Fin 2 → LittleContourSpace η,
      (∀ i z, ‖ContourC1Space.toBCF η (W i).val z‖ ≤ B * radScale R ρ k) →
      (∀ i z, e * radScale R ρ k ≤ ‖ContourC1Space.toBCF η (W i).val z‖) →
      (∀ i, ‖W i‖ ≤ radScale R ρ k * L) →
      ∃ Q : Fin 2 → LittleContourSpace η,
        (∀ i θ, LittleContourSpace.lift η (Q i) θ =
          P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N k k hkN S t (LittleContourSpace.lift η (W i) θ)) ∧
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ k) ≤
          Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 * ‖x k‖ +
            (finiteCurrentPolynomialForcingCoefficient (η : ℝ) e L Cb b Cd + Δ) *
              ρ ^ 6 * (1 + D) ^ 4 := by
  obtain ⟨Ct, Cd, hCt, hCd, hsource⟩ := P.exists_uniform_actualCurrent_complete_forcing_budget
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro η hη s A₀ b R ρ c B δ e a L Cb D C₀ K Δ hs hA hb hb1 hR hRmax hρ hρ1 hhalf
    ha ha16 hc hB he hL hCb hD hC₀ hK hΔ hζ hsepL hRchart hsmall
    N k hkN f T S hS t ht G x hx hq hgeom hchart hsupp hsep W hWmax hWmin hWL
  classical
  have hex (i : Fin 2) := hsource hη hs hA hb hb1 hR hRmax hρ hρ1 hhalf
    ha ha16 hc hB he hL hCb hD hC₀ hK hΔ hζ hsepL hRchart hsmall
    N k hkN S hS t ht G x hx hq hgeom hchart hsupp hsep (W i) (hWmax i) (hWmin i) (hWL i)
  choose Qi hQi hn using hex
  refine ⟨Qi, hQi, ?_⟩
  let Budget := Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 * ‖x k‖ +
    (finiteCurrentPolynomialForcingCoefficient (η : ℝ) e L Cb b Cd + Δ) * ρ ^ 6 * (1 + D) ^ 4
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hden : 0 < ampScale A₀ b k * radScale R ρ k := mul_pos hAk (radScale_pos hR hρ k)
  have hBudget0 : 0 ≤ Budget := (div_nonneg (norm_nonneg (Qi 0)) hden.le).trans (hn 0)
  change ‖Qi‖ / (ampScale A₀ b k * radScale R ρ k) ≤ Budget
  apply (div_le_iff₀ hden).mpr
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hBudget0 hden.le)).mpr
  intro i
  exact (div_le_iff₀ hden).mp (hn i)

end CircularMaterialTransferProfile
end Euler2D

end