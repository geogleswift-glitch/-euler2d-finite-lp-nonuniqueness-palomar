module

public import RequestProject.Euler.CircularFinitePrefixForcingSum
public import RequestProject.Euler.CircularFinitePrefixTorusRows
public import RequestProject.Euler.CircularFiniteInnerPlanarWeightedForcing
public import RequestProject.Euler.CircularFiniteInnerTorusWeightedForcing

/-! Constructing the complete actual off-self Little field. The real
active rows and the real rough inner cluster are combined before any
trajectory estimate; no total forcing budget is assumed. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finitePrefixOffSelfPhysicalField_eq_rows
    {s A₀ b R ρ : ℝ} (N k j : ℕ) (hkN : k ≤ N) (hjk : j ≤ k)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) :
    P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k (hjk.trans hkN) S t x =
      P.finitePrefixPlanarRowField s A₀ b R ρ N k j hkN S t x +
      velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x +
      P.finitePrefixTorusRowField s A₀ b R ρ N k S t x +
      actualTorusCorrectionVelocity (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x := by
  rw [P.finitePrefixPlanarRowField_eq_split N k j hkN hjk S t x]
  unfold finitePrefixOffSelfPhysicalField finitePrefixTorusRowField
  have hsum := Fin.sum_univ_eq_sum_range (fun l : ℕ => actualTorusCorrectionVelocity
    (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x) (k + 1)
  rw [hsum]

theorem exists_uniform_finitePrefix_complete_contourLittle_rows :
    ∃ Ct Cd : ℝ, 0 < Ct ∧ 0 < Cd ∧ ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 →
      ∀ {s A₀ b R ρ c B δ e a L Cb D C₀ : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 < b →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 < B → 0 < e →
      0 ≤ L → 0 ≤ Cb → 0 ≤ D → 1 ≤ C₀ →
      ∀ (N k j : ℕ) (hkN : k ≤ N) (hjk : j ≤ k),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S →
      ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ q : Fin (k + 1) → ℝ, (∀ l, 0 ≤ q l) →
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * q l) →
      (∀ l : Fin (k + 1), j < (l : ℕ) → 10 * radScale R ρ l ≤ e * radScale R ρ j) →
      (∀ l : Fin (k + 1), (l : ℕ) < j → 8 * (B * radScale R ρ j) ≤ c * radScale R ρ l) →
      (∀ l : Fin (k + 1), (5 / 4 : ℝ) * radScale R ρ l ≤ a) →
      (L + 1) * radScale R ρ j ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + D) ≤ a →
      (∀ x ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖x - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0) →
      8 * (Cb * ρ * radScale R ρ k * (1 + D)) ≤ e * radScale R ρ j →
      ∀ W : LittleContourSpace η,
      (∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * radScale R ρ j) →
      (∀ x, e * radScale R ρ j ≤ ‖ContourC1Space.toBCF η W.val x‖) →
      ‖W‖ ≤ radScale R ρ j * L →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k (hjk.trans hkN) S t (LittleContourSpace.lift η W θ)) ∧
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
          (∑ l : Fin (k + 1), if (l : ℕ) < j then
            finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L * b ^ (k - (l : ℕ)) *
              ρ ^ (2 * (j - (l : ℕ))) * q l else if j < (l : ℕ) then
            finiteInnerLabelLittleRowCoefficient (η : ℝ) e L * b ^ (k - (l : ℕ)) *
              ρ ^ (6 * ((l : ℕ) - j)) * q l else 0) +
          (∑ l : Fin (k + 1), if j ≤ (l : ℕ) then
            Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 *
              b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * q l else
            Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 *
              b ^ (k - (l : ℕ)) * ρ ^ (2 * (j - (l : ℕ))) * q l) +
          (C₀ * ρ ^ 6) ^ (k - j) *
            (((finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) *
              Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b))) +
            (Cd * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound *
              Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)))) := by
  obtain ⟨Ct, hCt, htorus⟩ := P.exists_uniform_finitePrefix_torus_contourLittle_rows
  obtain ⟨Cd, hCd, hdeep⟩ := P.exists_uniform_finiteInnerCluster_torus_weighted_contourLittle
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro η hη s A₀ b R ρ c B δ e a L Cb D C₀ hs hA hb hR hRmax hρ hρ1 hsmall
    ha ha16 hc hB he hL hCb hD hC₀ N k j hkN hjk f T S hS t ht G q hq0 hq
    hsepU hsepL hradius hgeom hchart hsupp hsep W hWmax hWmin hWL
  have hWL' : ‖W‖ ≤ L * radScale R ρ j := by simpa only [mul_comm L] using hWL
  obtain ⟨Qp, hQp, hnp⟩ := P.exists_finitePrefix_planar_contourLittle_rows hη hs hA hb
    hR hRmax hρ hρ1 N k j hkN hjk S t ht G q hq0 hq hc hB he hsepU hsepL W hWmax hWmin hWL
  obtain ⟨Qt, hQt, hnt⟩ := htorus hη hs hA hb hR hRmax hρ hρ1 ha ha16
    N k j hkN S t ht G q hq0 hq hradius hL hgeom W hWL'
  obtain ⟨Qdp, hQdp, hndp⟩ := P.exists_finiteInnerCluster_planar_weighted_contourLittle
    hη hs hA hb hR hRmax hρ hρ1 hsmall hCb hD hC₀ N k j hjk S hS t ht
    (by linarith) hsupp he hsep W hWmin hWL
  obtain ⟨Qdt, hQdt, hndt⟩ := hdeep hη hs hA hb hR hRmax hρ hρ1 hsmall
    ha ha16 hCb hD hC₀ N k j hjk S hS t ht hchart hsupp hL hgeom W hWL'
  refine ⟨Qp + Qdp + Qt + Qdt, ?_, ?_⟩
  · intro θ
    change LittleContourSpace.eval η (θ : ContourCircle) (Qp + Qdp + Qt + Qdt) = _
    simp only [map_add]
    change LittleContourSpace.lift η Qp θ + LittleContourSpace.lift η Qdp θ +
      LittleContourSpace.lift η Qt θ + LittleContourSpace.lift η Qdt θ = _
    rw [hQp, hQdp, hQt, hQdt,
      P.finitePrefixOffSelfPhysicalField_eq_rows N k j hkN hjk S t]
  · have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
    have hden : 0 < ampScale A₀ b k * radScale R ρ j := mul_pos hAk (radScale_pos hR hρ j)
    calc
      _ ≤ (‖Qp‖ + ‖Qdp‖ + ‖Qt‖ + ‖Qdt‖) / (ampScale A₀ b k * radScale R ρ j) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ = ‖Qp‖ / (ampScale A₀ b k * radScale R ρ j) +
          ‖Qt‖ / (ampScale A₀ b k * radScale R ρ j) +
          (‖Qdp‖ / (ampScale A₀ b k * radScale R ρ j) +
          ‖Qdt‖ / (ampScale A₀ b k * radScale R ρ j)) := by ring
      _ ≤ _ := (add_le_add (add_le_add hnp hnt) (add_le_add hndp hndt)).trans_eq (by ring)

end CircularMaterialTransferProfile
end Euler2D

end
