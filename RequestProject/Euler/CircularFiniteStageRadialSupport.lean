module

public import RequestProject.Euler.CircularFiniteRealRadialFeedback

/-! Genuine relative support of all actual inner labels on a finite
stage. The original real Euler radial input is fully supplied from
material outer geometry and the actual source mass bounds. Only the
explicit scalar barrier inequalities and starting geometry remain. -/

@[expose] public section

set_option maxHeartbeats 3300000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def finiteEulerRadialSelfBudget (C A₀ b R ρ : ℝ) (k : ℕ) : ℝ :=
  C * ampScale A₀ b k * radScale R ρ k * (ρ / b) / (1 - ρ / b)

def finiteEulerRadialFeedbackBudget (K A₀ b R ρ c d δ : ℝ) (k : ℕ) : ℝ :=
  ((32 / (15 * c ^ 4) * circularRadialPerturbationWeight) * δ / (1 - b * ρ ^ 2) +
    K * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8 * (b * ρ ^ 2) ^ k) *
      (ampScale A₀ b k / radScale R ρ k ^ 2)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteInnerActiveInitialLabels (s A₀ b R ρ : ℝ) (N k : ℕ) : Set R2 :=
  {y | y ∈ torusBox ∧ ∃ j ∈ Finset.Ico (k + 1) (N + 1),
    P.finitePeriodicLabel s A₀ b R ρ N j y ≠ 0}

theorem exists_uniform_actualFiniteEuler_stageInnerSupport :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {s A₀ b R ρ q T c d δ : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 < A₀) (_hb : 0 < b)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1)
        (_hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
        (_hsmall : ρ ^ 2 < b) (_houter : b * ρ ^ 2 < 1)
        (_hc : 0 < c) (_hd : 0 < d) (_hd16 : d * R ≤ 1 / 16) (_hδ : 0 ≤ δ),
      ∀ N k : ℕ, k ≤ N → ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ {a H a₀ a₁ B F : ℝ},
      0 ≤ a → a ≤ H → H ≤ T → 0 ≤ a₀ → a₀ ≤ a₁ → 0 < a₁ → 0 < B → B < 1 →
      B ≤ c * radScale R ρ k / 2 → B ≤ d * R →
      finiteEulerRadialSelfBudget C A₀ b R ρ k +
        finiteEulerRadialFeedbackBudget K A₀ b R ρ c d δ k * B ^ 3 < F →
      a₁ + F * (H - a) ≤ B →
      (∀ τ ∈ Icc a H, ∀ y ∈ torusBox, d * R < ‖y - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) τ y = 0) →
      (∀ τ ∈ Icc a H, P.FiniteOuterMaterialTube s R ρ N k S τ c δ) →
      (∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward a y - torusCenter‖ ≤ a₀) →
      ∀ τ ∈ Icc a H,
        (∀ j ∈ Finset.Ico (k + 1) (N + 1), ∀ y ∈ torusBox, B < ‖y - torusCenter‖ →
          S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) τ y = 0) ∧
        (∀ y ∈ torusBox, B < ‖y - torusCenter‖ →
          P.finiteInnerClusterSource s A₀ b R ρ N k S τ y = 0) := by
  obtain ⟨C, K, hC, hK, hfeedback⟩ := P.exists_uniform_actualFiniteEuler_realRadial_feedback
  refine ⟨C, K, hC, hK, ?_⟩
  intro s A₀ b R ρ q T c d δ _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hsmall houter hc hd hd16 hδ
    N k hk S hS a H a₀ a₁ B F ha haH hHT ha₀ ha₀₁ ha₁ hB hB1 hBcore hBchart hF hbudget hglobal G hstart τ hτ
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hden' : 0 < 1 - b * ρ ^ 2 := sub_pos.mpr houter
  have hdenMass : 0 < 1 - ρ ^ 2 / b := sub_pos.mpr ((div_lt_one hb).mpr hsmall)
  have hmass : 0 ≤ circularFiniteL1Coefficient b ρ := by
    unfold circularFiniteL1Coefficient finiteContourPatchMassBound
    exact add_nonneg (div_nonneg ENNReal.toReal_nonneg hdenMass.le)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) measureReal_nonneg))
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hV : 0 ≤ finiteEulerRadialSelfBudget C A₀ b R ρ k := by
    unfold finiteEulerRadialSelfBudget ampScale radScale
    positivity
  have hL : 0 ≤ finiteEulerRadialFeedbackBudget K A₀ b R ρ c d δ k := by
    unfold finiteEulerRadialFeedbackBudget ampScale radScale
    positivity
  let f₀ : Lp ℝ 2 μT := finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
    (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N
  have hradial : ∀ u ∈ Icc a H, ∀ y : R2, ‖y - torusCenter‖ ≤ B →
      inner ℝ (y - torusCenter)
        (particleVelocityRepresentative f₀ S.backward S.backward_area u y) ≤
      ‖y - torusCenter‖ * (finiteEulerRadialSelfBudget C A₀ b R ρ k +
        finiteEulerRadialFeedbackBudget K A₀ b R ρ c d δ k * ‖y - torusCenter‖ ^ 3) := by
    intro u hu y hy
    let z := normalizedComplexCoordinate 1 y
    have hnorm : ‖z‖ = ‖y - torusCenter‖ := by
      dsimp only [z]
      rw [normalizedComplexCoordinate_one, norm_planeComplexEquiv]
    have hpoint : complexTorusPoint z = y := complexTorusPoint_normalizedComplexCoordinate_one y
    have hh := hfeedback hs hA hb hR hRmax hρ hρ1 hρb hq hqE hsmall houter hc hd hd16 hδ N k hk S hS
      u ⟨ha.trans hu.1, hu.2.trans hHT⟩ (hglobal u hu) (G u hu) z
      (by rw [hnorm]; exact hy.trans hBcore) (by rw [hnorm]; exact hy.trans hBchart)
    rw [hpoint, hnorm] at hh
    exact hh
  have hAbox : P.finiteInnerActiveInitialLabels s A₀ b R ρ N k ⊆ torusBox := fun y hy => hy.1
  have hlabels : ∀ j ∈ Finset.Ico (k + 1) (N + 1), ∀ y ∈ torusBox, B < ‖y - torusCenter‖ →
      S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) τ y = 0 := by
    intro j hj
    apply S.transportedScalar_support_of_stage_radial_barrier ha haH hHT ha₀ ha₀₁ ha₁ hB hB1 hV hL hF hbudget
      hradial hAbox _ hstart hτ
    intro y hy hn
    by_contra hne
    exact hn ⟨hy, j, hj, hne⟩
  refine ⟨hlabels, ?_⟩
  intro y hy hn
  exact Finset.sum_eq_zero (fun j hj => hlabels j hj y hy hn)

end CircularMaterialTransferProfile
end Euler2D

end
