module

public import RequestProject.Euler.CircularControlledLookbackCapture
public import RequestProject.Euler.CircularCoupledControlledEntranceFamily

/-! Retain the original Euler solution, selected canonical target and
literal physical moment histories with R=rho^10, A0=cA*(1+xi).
Normalized constants precede the later amplitude coefficient cA. -/

@[expose] public section

set_option maxHeartbeats 32000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def HasActualCoupledDeepestLookbackEnvelopeFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0) (cA D δ εgeom : ℝ) (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (Lback Henv Cerror ξ : ℝ) : Prop :=
  let ρ := Real.exp (-ξ)
  let hρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  let hR := pow_pos hρ 10
  let A₀ := cA * (1 + ξ)
  ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧
  ∀ N : ℕ, D / ampScale A₀ b N < T ∧
    let f := finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N
    ∃ S : BoundedEulerParticleSystem f T,
      IsFourfoldBoundedEulerParticleSystem S ∧
      IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f S.backward S.backward_area) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) ∧
      ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ le_rfl S
          (D / ampScale A₀ b N) X ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          weightedFamilyNorm (2 * ρ ^ 6) N
            (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X τ) ≤ 1) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X τ - littleCircularMaterialContours hγ hγ1 τ‖ ≤
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * τ)) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X τ - littleCircularMaterialContours hγ hγ1 τ‖ ≤ εgeom / 2) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ τ (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X τ) -
              littleCircularReference hγ hγ1)
          ‖vc - gseq (circularConstrainedUnstableProjectionCLM hγ hγ1.le vc) 0‖ ≤ Cerror * ρ ^ 3) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ τ (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X τ) -
                littleCircularReference hγ hγ1))‖ = δ → Lback < τ) ∧
        HasFirstCircularCoRotatedCaptureSection hγ hγ1
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X) D δ ∧
        ∃ τ ∈ Ioc (0 : ℝ) D,
          τ / ampScale A₀ b N ∈ Ioc (0 : ℝ) (D / ampScale A₀ b N) ∧
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X τ -
                littleCircularMaterialContours hγ hγ1 τ))‖ = δ ∧
          ∀ u ∈ Ico (0 : ℝ) τ,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X u -
                  littleCircularMaterialContours hγ hγ1 u))‖ < δ

theorem actual_coupled_deepest_envelope_family_after_of_small_seed
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    {hq : 0 < q} {hqE : 2 ≤ ENNReal.ofReal q}
    {b : ℝ≥0} {s : ℝ} {hs : s ≤ 0} {cA D δ εgeom : ℝ}
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    {Lback Henv Cerror ξ : ℝ} (hH : 0 ≤ Henv)
    (hsmall : (‖circularConstrainedUnstableProjectionCLM hγ hγ1.le‖ *
      ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖) * Henv *
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * Lback) < δ)
    (hbase : P.HasActualCoupledDeepestCapturedEnvelopeFamilyAt (T := T) hq hqE
      b s hs cA D δ εgeom gseq Henv Cerror ξ) :
    P.HasActualCoupledDeepestLookbackEnvelopeFamilyAt (T := T) hq hqE
      b s hs cA D δ εgeom gseq Lback Henv Cerror ξ := by
  dsimp only [HasActualCoupledDeepestCapturedEnvelopeFamilyAt,
    HasActualCoupledDeepestLookbackEnvelopeFamilyAt] at hbase ⊢
  obtain ⟨hρ, hlp, hfinite⟩ := hbase
  refine ⟨hρ, hlp, ?_⟩
  intro N
  obtain ⟨htime, S, hS, hweak, harea, X, hX, hweighted, hforward,
    hnear, hgraph, hcohit, hmoving⟩ := hfinite N
  refine ⟨htime, S, hS, hweak, harea, X, hX, hweighted, hforward,
    hnear, hgraph, ?_, hcohit, hmoving⟩
  intro τ hτ hsection
  exact circularCapture_section_time_gt_of_small_seed hγ hγ1 hH (norm_nonneg _)
    (canonicalPrefixAlignedCurrentCell (cA * (1 + ξ)) b (Real.exp (-ξ) ^ 10) (Real.exp (-ξ)) N 0 X)
    (hforward τ hτ) hsection hsmall
theorem exists_actual_deepest_envelope_family_with_coupled_lookback {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Y)
    (hd : ContDiffAt ℝ 2 (fun W => Y W period) (littleCircularReference hγ hγ1))
    (hfix : Y (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Y W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Y W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r₀ / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (gseq α 0))
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 < T)
    (δmax εgeom Kextra : ℝ) (hδmax : 0 < δmax) (hεgeom : 0 < εgeom) (hKextra : 0 ≤ Kextra) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ δ > 0, δ < δmax ∧ ∃ Henv > 0,
        ∀ Lback : ℝ, ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period);
          ∃ hs : s ≤ 0, ∃ D > 0, ∃ Cerror > 0,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ εgeom / 2 ∧
            ∀ cA > 0, D / cA < T →
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualCoupledDeepestLookbackEnvelopeFamilyAt (T := T) hq hqE
                b s hs cA D δ εgeom gseq Lback Henv Cerror ξ := by
  obtain ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, hδmax', Henv, hHenv, hfamilies⟩ :=
    P.exists_actual_deepest_envelope_family_with_coupled_entrance
      hRflow hr₀ hY hd hfix harea hg hsamples hq hqE hT
      δmax εgeom Kextra hδmax hεgeom hKextra
  refine ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, hδmax', Henv, hHenv, ?_⟩
  intro Lback seedMax hseedMax nMin
  let Ccoef := (‖circularConstrainedUnstableProjectionCLM hγ hγ1.le‖ *
    ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖) * Henv
  have hCcoef : 0 ≤ Ccoef := by dsimp only [Ccoef]; positivity
  have hdenom : 0 < (Ccoef + 1) * Real.exp (sigma * Lback) :=
    mul_pos (by linarith only [hCcoef]) (Real.exp_pos _)
  let seedBound := min seedMax (δ / ((Ccoef + 1) * Real.exp (sigma * Lback)))
  have hseedBound : 0 < seedBound := lt_min hseedMax (div_pos hδ hdenom)
  obtain ⟨n, hn, hdata⟩ := hfamilies seedBound hseedBound nMin
  dsimp only at hdata
  obtain ⟨hs, D, hD, Cerror, hCerror, hseed, hterminalEnvelope, hfamily⟩ := hdata
  let s := -(n : ℝ) * (period + period)
  let seed := ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
    (circularConstraintProjectionToTangentCLM hγ hγ1.le
      (P.ancient s - littleCircularReference hγ hγ1))‖
  have hseedNonneg : 0 ≤ seed := norm_nonneg _
  have hseedMax' : seed < seedMax := hseed.trans_le (min_le_left _ _)
  have hseedBudget : seed < δ / ((Ccoef + 1) * Real.exp (sigma * Lback)) :=
    hseed.trans_le (min_le_right _ _)
  have hproduct : seed * ((Ccoef + 1) * Real.exp (sigma * Lback)) < δ :=
    (lt_div_iff₀ hdenom).mp hseedBudget
  have hsmall : Ccoef * seed * Real.exp (sigma * Lback) < δ := by
    calc
      _ ≤ (Ccoef + 1) * seed * Real.exp (sigma * Lback) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : Ccoef ≤ Ccoef + 1) hseedNonneg)
          (Real.exp_pos _).le
      _ = seed * ((Ccoef + 1) * Real.exp (sigma * Lback)) := by ring
      _ < δ := hproduct
  refine ⟨n, hn, hs, D, hD, Cerror, hCerror, hseedMax', hterminalEnvelope, ?_⟩
  intro cA hcA hTimeBase
  filter_upwards [hfamily cA hcA hTimeBase] with ξ hfamilyξ
  exact P.actual_coupled_deepest_envelope_family_after_of_small_seed
    hHenv.le hsmall hfamilyξ

end CircularMaterialTransferProfile
end Euler2D