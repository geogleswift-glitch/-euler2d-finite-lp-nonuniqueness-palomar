module

public import RequestProject.Euler.TorusPartialCanonicalForcing
public import RequestProject.Euler.EulerLabelSupportEndpointWindow
public import RequestProject.Euler.CircularFiniteInnerLabelForcing
public import RequestProject.Euler.CircularFiniteStageRadialSupport

/-! An actual finite Euler source has a genuine support window beyond
an intermediate endpoint whenever its inner particles have a strict
radial buffer there. Combined with the active closed-tube estimate,
this extends the same canonical partial contour equation. The local
extension time may depend on the original finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 5500000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actualPrefix_continuation_of_particle_buffer
    {s A₀ b R ρ q T Hglob D H a ai₀ ai η : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hglobT : Hglob ≤ T) (hD : 0 < D) (hDglob : D < Hglob) (hH : 0 < H)
    (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hai₀ : 0 ≤ ai₀) (hbuffer : ai₀ < ai) (hai1 : ai < 1)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    (hρa : ρ ≤ cellA / 4)
    (hsize : R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4)
    (N k : ℕ) (_hk : k ≤ N)
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T)
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    (hglobal : ∀ t ∈ Icc (0 : ℝ) Hglob, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0)
    (hstart : ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
      ‖S.forward D y - torusCenter‖ ≤ ai₀)
    (hpast : ∀ t ∈ Icc (0 : ℝ) D, ∀ x ∈ torusBox,
      ai₀ < ‖x - torusCenter‖ → P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0)
    (hsep : ∀ p : FiniteCircularIndex k, 32 * ai ≤ finiteCircularInterfaceRadius R ρ p)
    (Z : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hd : ∀ t ∈ Ico (0 : ℝ) D, HasDerivAt Z
      (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceStrength A₀ b) (Z t) +
          S.actualPartialContourForcing (P.finiteInnerInitialLabel s A₀ b R ρ N k) t (Z t)) t)
    (hmem : ∀ t ∈ Ico (0 : ℝ) D,
      IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (Z t) ∧ ‖Z t‖ < a / 4 ∧
      IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (Z t))
    (htube : ∀ t ∈ Ioo (0 : ℝ) D, ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
      ‖contourParameterShiftC1 (β p) (Z t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
        η * radScale R ρ p.1) :
    ∃ δ > 0, δ ≤ H ∧ D + δ ≤ Hglob ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ), ∀ x ∈ torusBox,
        ai < ‖x - torusCenter‖ → P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0) ∧
      ∃ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      (∀ t ∈ Ico (0 : ℝ) D, Y t = Z t) ∧
      ContinuousOn Y (Icc (0 : ℝ) (D + δ)) ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ), HasDerivAt Y
        (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceStrength A₀ b) (Y t) +
            S.actualPartialContourForcing (P.finiteInnerInitialLabel s A₀ b R ρ N k) t (Y t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ),
        IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Y t) ∧ ‖Y t‖ < a / 4 ∧
        IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Y t)) ∧
      ∀ t ∈ Icc (0 : ℝ) (D + δ), ∀ p θ,
        HasDerivAt (fun u => LittleContourSpace.lift γ (Y u p) θ)
          (contourBoundaryField (finiteCircularInterfaceStrength A₀ b)
              (fun j => LittleContourSpace.lift γ (Y t j)) p θ +
            S.physicalLabelComplexField (P.finiteInnerInitialLabel s A₀ b R ρ N k) t
              (LittleContourSpace.lift γ (Y t p) θ)) t := by
  have hf := P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N
  have hB : ∀ᵐ x ∂μT,
      ‖finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x‖ ≤
          finiteInitialDensityBound A₀ b N := by
    filter_upwards [hf] with x hx
    rw [hx]
    exact P.norm_finiteInitialPlanarDensity_le hs N _
  have hqinitial : ∀ x ∈ torusBox,
      x ∉ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k →
        P.finiteInnerInitialLabel s A₀ b R ρ N k x = 0 := by
    intro x hx hn
    apply Finset.sum_eq_zero
    intro j hj
    by_contra hne
    exact hn ⟨hx, j, hj, hne⟩
  obtain ⟨δs, hδs, hδsT, hsource⟩ := S.exists_extended_transported_support_window
    hD.le (hDglob.trans_le hglobT) (finiteInitialDensityBound_nonneg A₀ b N) hB
    hai₀ hbuffer hai1 (fun _ hx => hx.1) hqinitial hstart hpast
  let ε := min (D + δs) Hglob
  have hDε : D < ε := lt_min (by linarith) hDglob
  have hε : 0 < ε := hD.trans hDε
  have hεT : ε ≤ T := (min_le_right _ _).trans hglobT
  have hinner : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      ai < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInnerInitialLabel s A₀ b R ρ N k) t x = 0 := by
    intro t ht x hx hxt
    exact hsource t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩ x hx hxt
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_torusBox] with x hfx hx
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx).trans hfx.symm
  have hmean : (∫ x in torusBox,
      finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x) = 0 :=
    (integral_congr_ae (scalarLpLowerToTwo_ae hqE _)).trans
      (P.integral_finiteBaseTorusLp_zero hs hR hRmax hρ hρ1 hq N)
  obtain ⟨hqlp, hqper, hqbound⟩ := P.finiteInnerInitialLabel_bounds hs hA hb hR hRmax hρ hρ1 N k
  obtain ⟨δ, hδ, hδH, hδε, Y, hYZ, hYc, hYd, hYmem, hYmat⟩ :=
    S.exists_finiteCircular_actual_partial_continuation hS hwf
      (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
      (P.finiteInitialPeriodicDensity_quarterTurn hs N) hmean
      hqlp hqper (P.finiteInnerInitialLabel_quarterTurn hs N k)
      (P.integral_finiteInnerInitialLabel_zero hs hA hb hR hRmax hρ hρ1 N k) hqbound
      hε hεT ha ha16
      (fun t ht => hglobal t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩)
      (hai₀.trans hbuffer.le) hai1 hinner hγ hγ1 hR hρ hρ1 hη hηa hsize hρa hηgap
      hsep hD hDε hH (finiteCircularInterfaceStrength A₀ b) Z hd hmem htube
  refine ⟨δ, hδ, hδH, hδε.trans (min_le_right _ _), ?_, Y, hYZ, hYc, hYd, hYmem, hYmat⟩
  intro t ht x hx hxt
  exact hinner t ⟨ht.1, ht.2.trans hδε⟩ x hx hxt

end CircularMaterialTransferProfile
end Euler2D

end
