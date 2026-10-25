module

public import RequestProject.Euler.TorusPartialCanonicalTrajectory
public import RequestProject.Euler.CircularFinitePartialMaterialIdentification

/-! Two valid actual active-prefix trajectories are the same material
particles of the same original Euler solution. This proves overlap
compatibility without assuming Lipschitz regularity of the full inner
velocity on a ball crossing its source. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualPrefix_canonical_uniqueness :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob a c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      ∀ {N k : ℕ} (hk : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      let qinner := P.finiteInnerInitialLabel s A₀ b R ρ N k
      let F := S.actualPartialPhaseField qinner hγ hγ1
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceStrength A₀ b)
      let U := S.actualPartialPhaseDomain qinner
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob
      let Zinit : FiniteCircularIndex k → LittleContourSpace γ := fun p =>
        finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hk p)
      ∀ {A B : ℝ} {α β : ℝ → FiniteCircularIndex k → LittleContourSpace γ},
        IsBanachTimeDomainTrajectoryOn F U Zinit A α →
        IsBanachTimeDomainTrajectoryOn F U Zinit B β →
        EqOn α β (Icc (0 : ℝ) (min A B)) := by
  obtain ⟨C, hC, hidentify⟩ := P.exists_uniform_finiteEuler_partial_material_identification
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob a c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR N k hk S
  dsimp only
  intro A B α β hα hβ
  let D := min A B
  by_cases hD : 0 < D
  · have hαD := hα.mono (min_le_left A B)
    have hβD := hβ.mono (min_le_right A B)
    have hDglob : D ≤ Hglob := (hαD.mem D ⟨hD.le, le_rfl⟩).1.2
    have hDT : D ≤ T := hDglob.trans hglobT
    have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
    have hcoef : 0 ≤ C * A₀ / (1 - ρ / b) := div_nonneg (mul_nonneg hC.le hA) hden.le
    have hcD : (5 / 4 : ℝ) + (C * A₀ / (1 - ρ / b)) * D < c :=
      lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_of_nonneg_left hDglob hcoef)) hc
    have hboundary (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
        (hX : IsBanachTimeDomainTrajectoryOn
          (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
            (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
            (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
            (finiteCircularInterfaceStrength A₀ b))
          (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
            (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
          (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
            (finiteCircularPrefixIndex hk p)) D X) :
        ∀ t ∈ Icc (0 : ℝ) D, ∀ p θ,
          S.forward t (complexTorusPoint (LittleContourSpace.lift γ (X 0 p) θ)) =
            complexTorusPoint (LittleContourSpace.lift γ (X t p) θ) := by
      let Z : ℝ → FiniteCircularIndex k → ContourC1Space γ := fun t p => (X t p).val
      have hZ0 : Z 0 = fun p =>
          (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
            (finiteCircularPrefixIndex hk p)).val := by
        exact congrArg (fun Y : FiniteCircularIndex k → LittleContourSpace γ => fun p => (Y p).val) hX.initial
      have hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
          ‖contourParameterShiftC1 (β p) (Z t p) - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ <
            finiteCircularInterfaceRadius R ρ p / 4 := by
        intro t ht
        exact (hX.mem t ht).2.2.2.1
      have hZc (p : FiniteCircularIndex k) : ContinuousOn (fun t => Z t p) (Icc (0 : ℝ) D) :=
        (LittleContourSpace.inclusion γ).continuous.comp_continuousOn
          ((continuous_apply p).comp_continuousOn hX.continuous)
      have hmat : ∀ t ∈ Icc (0 : ℝ) D, ∀ p θ,
          HasDerivAt (fun u => ContourC1Space.lift γ (Z u p) θ)
            (contourC1BoundaryField (finiteCircularInterfaceStrength A₀ b) (Z t) p θ +
              S.physicalLabelComplexField (P.finiteInnerInitialLabel s A₀ b R ρ N k) t
                (ContourC1Space.lift γ (Z t p) θ)) t := by
        intro t ht
        exact (S.actualPartialPhaseField_material_iff hγ hγ1
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceStrength A₀ b) (hX.hasDerivAt t ht) (hX.mem t ht).2.1).mpr
            (hX.mem t ht).2.2.2.2
      have hi := hidentify hs hA hb hR hRmax hρ hρ1 hρb hq hqE hD.le hDT hcD hcR
        hk S Z hZ0 hphase hZc hmat
      intro t ht
      exact (hi t ht).1
    intro t ht
    funext p
    apply littleContour_eq_of_lift_eq
    intro θ
    apply centeredComplexHomeomorph.injective
    change complexTorusPoint (LittleContourSpace.lift γ (α t p) θ) =
      complexTorusPoint (LittleContourSpace.lift γ (β t p) θ)
    rw [← hboundary α hαD t ht p θ, ← hboundary β hβD t ht p θ, hαD.initial, hβD.initial]
  · intro t ht
    have ht0 : t = 0 := le_antisymm (ht.2.trans (le_of_not_gt hD)) ht.1
    rw [ht0, hα.initial, hβ.initial]

end CircularMaterialTransferProfile
end Euler2D

end
