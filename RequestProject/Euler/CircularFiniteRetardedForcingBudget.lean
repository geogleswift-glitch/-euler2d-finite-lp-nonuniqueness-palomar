module

public import RequestProject.Euler.CircularFiniteRetardedMaterialTube
public import RequestProject.Euler.CircularFiniteTorusCorrectionBudget
public import RequestProject.Euler.TorusPhysicalCorrectionIdentity

/-! The complete actual forcing consists of the same-S ancestor
residual, same-S inner source, and same-S torus correction. Its
retarded feedback coefficient and its rho-six/R-eight baselines are
proved from those sources, rather than supplied as forcing bounds. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric Filter
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualRetardedContourForcing_budget :
    ∃ Ctorus : ℝ, 0 < Ctorus ∧ ∀ {s A₀ b R ρ q T c B L δ Cb D e d : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
        (hsmall : ρ ^ 2 < b) (houter : b * ρ ^ 2 < 1)
        (hc : 0 < c) (hB : 0 < B) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
        (hCb : 0 ≤ Cb) (hD : 0 ≤ D) (he : 0 < e) (hd : 0 < d) (hd16 : d * R ≤ 1 / 16),
      ∀ (N k : ℕ) (hk : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      (∀ x ∈ torusBox, d * R < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0) →
      P.FiniteOuterMaterialTube s R ρ N (k - 1) S t c δ →
      Cb * ρ * radScale R ρ k * (1 + D) < 1 →
      (∀ x ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖x - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0) →
      8 * B * ρ ≤ c → 8 * (Cb * ρ * (1 + D)) ≤ e →
      (L + 1) * radScale R ρ k ≤ (d * R) / 2 →
      ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 → ∀ W Qt : LittleContourSpace η,
      (∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * radScale R ρ k) →
      (∀ x, e * radScale R ρ k ≤ ‖ContourC1Space.toBCF η W.val x‖) →
      ‖W‖ ≤ radScale R ρ k * L →
      (∀ θ, LittleContourSpace.lift η Qt θ =
        planeComplexEquiv (S.correctionLabelField t (complexTorusPoint (LittleContourSpace.lift η W θ)))) →
      ∃ Qa Qi : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Qa θ =
          ∑ j : Fin k, velocityC
            (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (finiteAncestorIndex hk j) S t)
            (LittleContourSpace.lift η W θ)) ∧
        (∀ θ, LittleContourSpace.lift η Qi θ =
          velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
            (LittleContourSpace.lift η W θ)) ∧
        ‖Qa + Qi + Qt‖ / (ampScale A₀ b k * radScale R ρ k) ≤
          (interiorContourNormBudget (η : ℝ) 1 c B L *
            (4 * Real.pi * circularRadialPerturbationWeight)) *
            (δ * (b * ρ ^ 2) / (1 - b * ρ ^ 2)) +
          (finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) *
            Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)) +
          Ctorus * torusCorrectionContourBudget (η : ℝ) L * d ^ 4 *
            circularFiniteL1Coefficient b ρ * R ^ 8 * (b * ρ ^ 2) ^ k := by
  obtain ⟨Ctorus, hCtorus, htorus⟩ := P.exists_finiteEuler_uniformTorusCorrection_labelBudget
  refine ⟨Ctorus, hCtorus, ?_⟩
  intro s A₀ b R ρ q T c B L δ Cb D e d _ hs hA hb hR hRmax hρ hρ1 hq hqE
    hsmall houter hc hB hL hδ hCb hD he hd hd16 N k hk S hS t ht hsupp G ha1 hinner
    hsepOut hsepIn hgeom η hη W Qt hWout hWin hW hQt
  obtain ⟨Qa, hQa, hna⟩ := P.exists_finiteAncestorResidual_contourLittle_of_prefix hη hs hA hb
    hR hRmax hρ hρ1 houter hδ N k hk S t ht hc hB G hsepOut W hWout hW
  obtain ⟨Qi, hQi, hni⟩ := P.exists_finiteInnerCluster_contourLittle_rhoSix hη hs hA hb hR hRmax
    hρ hρ1 hsmall N k S hS ht hCb hD ha1 hinner he hsepIn W hWin hW
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with x hx hxbox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hxbox).trans hx.symm
  have hQt' (θ : ℝ) : LittleContourSpace.lift η Qt θ =
      actualTorusCorrectionVelocity (S.physicalComplexSource
        (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) (LittleContourSpace.lift η W θ) :=
    (hQt θ).trans (S.actualTorusCorrectionVelocity_physicalComplexSource hwf ht _).symm
  have hnt := htorus hs hA hb hR hRmax hρ hρ1 hq hqE hsmall hd hd16 N S hS t ht hsupp
    hη k hL hgeom W (by simpa only [mul_comm] using hW) Qt hQt'
  have hden : 0 ≤ ampScale A₀ b k * radScale R ρ k := by
    have hr := (radScale_pos hR hρ k).le
    have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
    exact mul_nonneg hAk.le hr
  refine ⟨Qa, Qi, hQa, hQi, ?_⟩
  calc
    _ ≤ (‖Qa‖ + ‖Qi‖ + ‖Qt‖) / (ampScale A₀ b k * radScale R ρ k) :=
      div_le_div_of_nonneg_right ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) hden
    _ = ‖Qa‖ / (ampScale A₀ b k * radScale R ρ k) +
        ‖Qi‖ / (ampScale A₀ b k * radScale R ρ k) +
        ‖Qt‖ / (ampScale A₀ b k * radScale R ρ k) := by rw [add_div, add_div]
    _ ≤ _ := add_le_add (add_le_add hna hni) hnt

end CircularMaterialTransferProfile
end Euler2D

end
