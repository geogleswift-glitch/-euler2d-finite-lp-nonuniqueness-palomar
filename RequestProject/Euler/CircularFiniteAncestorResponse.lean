module

public import RequestProject.Euler.CircularRetardedBudgetFeedback
public import RequestProject.Euler.CircularAncestorTimeRescaling
public import RequestProject.Euler.BanachDelayedFamilyResponse

/-! The actual finite ancestor family closes its common response
maximum. The equation and its complete forcing budget are derived
from the true same-S raw material derivative and source lifts. -/

@[expose] public section

set_option maxHeartbeats 14000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric Filter
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

local instance actualAncestorResponseReal_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := (smul_smul a b Z).symm

def actualAncestorRotatedContour {γ : ℝ≥0} (A₀ b : ℝ) {N : ℕ}
    (W : Fin (N + 1) → ℝ → Fin 2 → LittleContourSpace γ) (j : Fin (N + 1)) (t : ℝ) :
    Fin 2 → LittleContourSpace γ :=
  rigidRotationGauge (finiteAncestorAngularVelocity A₀ b j) 0 t • W j t

theorem exp_undo_rigidRotationGauge (Ω t : ℝ) :
    exp ((((Ω * t : ℝ) : ℂ)) * I) * rigidRotationGauge Ω 0 t = 1 := by
  unfold rigidRotationGauge
  rw [← exp_add]
  convert exp_zero using 1
  congr 1
  push_cast
  ring

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualAncestor_response_bound :
    ∃ Ctorus : ℝ, 0 < Ctorus ∧ ∀ {s A₀ b R ρ q T c B L δ₀ Cb D e d H : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
        (hsmall : ρ ^ 2 < b) (houter : b * ρ ^ 2 < 1)
        (hc : 0 < c) (hB : 0 < B) (hL : 0 ≤ L)
        (hCb : 0 ≤ Cb) (hD : 0 ≤ D) (he : 0 < e) (hd : 0 < d) (hd16 : d * R ≤ 1 / 16),
      ∀ (N k : ℕ) (hk : k ≤ N), 0 < k → ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → 0 ≤ H → H ≤ T →
      ∀ (W Qt V : Fin (N + 1) → ℝ → Fin 2 → LittleContourSpace γ)
        (z : Fin (N + 1) → ℝ → Fin 2 → LittleContourSpace γ),
      (∀ j t, z j t = radScale R ρ j • W j t) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → W j 0 = littleCircularReference hγ hγ1) →
      (∀ t ∈ Icc (0 : ℝ) H, ∀ x ∈ torusBox, d * R < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0) →
      ∀ G : ∀ t ∈ Icc (0 : ℝ) H, P.FiniteOuterMaterialTube s R ρ N (k - 1) S t c δ₀,
      (∀ t (ht : t ∈ Icc (0 : ℝ) H) (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k - 1) i,
        (G t ht).contours (j, i) = radScale R ρ j • (W j t i).val) →
      (∀ t ∈ Icc (0 : ℝ) H,
        circularRetardedPrefixDeviation hγ hγ1 (k - 1)
          (fun j => actualAncestorRotatedContour A₀ b W j t) (fun j => ampScale A₀ b j * t) ≤ cellA / 4) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → ∀ t ∈ Icc (0 : ℝ) H,
        Cb * ρ * radScale R ρ j * (1 + D) < 1 ∧
        (∀ x ∈ torusBox, Cb * ρ * radScale R ρ j * (1 + D) < ‖x - torusCenter‖ →
          P.finiteInnerClusterSource s A₀ b R ρ N j S t x = 0)) →
      8 * B * ρ ≤ c → 8 * (Cb * ρ * (1 + D)) ≤ e →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → (L + 1) * radScale R ρ j ≤ (d * R) / 2) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → ∀ t ∈ Icc (0 : ℝ) H,
        W j t ∈ circularQuarterPhaseDomain hγ hγ1 ∧
        (∀ i x, ‖ContourC1Space.toBCF γ (W j t i).val x‖ ≤ B) ∧
        (∀ i x, e ≤ ‖ContourC1Space.toBCF γ (W j t i).val x‖) ∧ ‖W j t‖ ≤ L) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → ∀ t ∈ Icc (0 : ℝ) H, ∀ i θ,
        ∀ l : Fin (j : ℕ), ‖radScale R ρ j • LittleContourSpace.lift γ (W j t i) θ‖ ≤
          cellA * radScale R ρ l) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → ∀ t ∈ Icc (0 : ℝ) H, ∀ i θ,
        LittleContourSpace.lift γ (Qt j t i) θ =
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (radScale R ρ j • LittleContourSpace.lift γ (W j t i) θ)))) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → ∀ t ∈ Icc (0 : ℝ) H,
        HasDerivAt (z j) (V j t) t ∧
        (∀ i θ, LittleContourSpace.lift γ (V j t i) θ =
          velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
            (radScale R ρ j • LittleContourSpace.lift γ (W j t i) θ) +
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (radScale R ρ j • LittleContourSpace.lift γ (W j t i) θ))))) →
      ∀ (U : Set (Fin 2 → LittleContourSpace γ)) (Kself : ℝ≥0),
      LipschitzOnWith Kself (circularBanachField hγ hγ1) U →
      (∀ t : ℝ, littleCircularMaterialContours hγ hγ1 t ∈ U) →
      (∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → ∀ t ∈ Icc (0 : ℝ) H,
        actualAncestorRotatedContour A₀ b W j t ∈ U) →
      2 * (b * ampScale A₀ b k * H * Real.exp (b * ampScale A₀ b k * (Kself : ℝ) * H)) *
        finiteRetardedAncestorFeedback (γ : ℝ) b ρ c B L ≤ 1 →
      ∀ j : Fin (N + 1), (j : ℕ) ≤ k - 1 → ∀ t ∈ Icc (0 : ℝ) H,
        ‖actualAncestorRotatedContour A₀ b W j t -
          littleCircularMaterialContours hγ hγ1 (ampScale A₀ b j * t)‖ ≤
        2 * (b * ampScale A₀ b k * H * Real.exp (b * ampScale A₀ b k * (Kself : ℝ) * H)) *
          finiteRetardedSourceBaseline (γ : ℝ) Ctorus b R ρ L Cb D e d := by
  obtain ⟨Ctorus, hCtorus, hpoint⟩ := P.exists_uniform_actualRetardedPhysical_derivative_budget
  refine ⟨Ctorus, hCtorus, ?_⟩
  intro s A₀ b R ρ q T c B L δ₀ Cb D e d H _ hs hA hb hb1 hR hRmax hρ hρ1 hq hqE
    hsmall houter hc hB hL hCb hD he hd hd16 N k hk hk0 S hS hH hHT W Qt V z hscale hW0
    hglobal G hGscale hQsmall hinner hsepOut hsepIn hgeom hW hx hQt hV U Kself hLip hcU hyU hfeedback
  let J := {j : Fin (N + 1) // (j : ℕ) ≤ k - 1}
  let y : J → ℝ → Fin 2 → LittleContourSpace γ := fun j => actualAncestorRotatedContour A₀ b W j
  let c₀ : J → ℝ → Fin 2 → LittleContourSpace γ := fun j t =>
    littleCircularMaterialContours hγ hγ1 (ampScale A₀ b j * t)
  let a : J → ℝ≥0 := fun j => ⟨ampScale A₀ b j, (div_pos hA (pow_pos hb j)).le⟩
  let bspeed : ℝ≥0 := ⟨b * ampScale A₀ b k, by unfold ampScale; positivity⟩
  let Base := finiteRetardedSourceBaseline (γ : ℝ) Ctorus b R ρ L Cb D e d
  let Feedback := finiteRetardedAncestorFeedback (γ : ℝ) b ρ c B L
  have ha (j : J) : a j ≤ bspeed := by
    have hjlt : ((j : Fin (N + 1)) : ℕ) < k := by have hj := j.property; omega
    have hh := (ancestor_ampScale_ratio_le hA hb hb1 hjlt).2
    exact (div_le_iff₀ (div_pos hA (pow_pos hb k))).mp hh
  have hphys (j : Fin (N + 1)) (t : ℝ) :
      (fun u => rigidRotationGauge (finiteAncestorAngularVelocity A₀ b j / ampScale A₀ b j) 0 u •
        normalizedPhysicalCurve (ampScale A₀ b j) (radScale R ρ j) 0 (z j) u)
        (ampScale A₀ b j * t) = actualAncestorRotatedContour A₀ b W j t := by
    have hAj : ampScale A₀ b j ≠ 0 := (div_pos hA (pow_pos hb j)).ne'
    have hrj : radScale R ρ j ≠ 0 := (radScale_pos hR hρ j).ne'
    have ht : physicalTimeFromNormalized (ampScale A₀ b j) 0 (ampScale A₀ b j * t) = t := by
      unfold physicalTimeFromNormalized
      field_simp [hAj]
      <;> simp
    change rigidRotationGauge _ 0 _ • ((radScale R ρ j)⁻¹ • z j (physicalTimeFromNormalized _ 0 _)) = _
    rw [rigidRotationGauge_normalized_physical_time hAj, ht, hscale j t, inv_smul_smul₀ hrj]
    rfl
  have hex : ∀ (j : J) (t : ℝ), ∃ p : Fin 2 → LittleContourSpace γ,
      t ∈ Icc (0 : ℝ) H →
        HasDerivAt (y j) ((a j : ℝ) • (circularBanachField hγ hγ1 (y j t) + p)) t ∧
        ‖p‖ ≤ Base + Feedback * ‖fun i : J => y i t - c₀ i t‖ := by
    intro j t
    by_cases ht : t ∈ Icc (0 : ℝ) H
    · have hj := j.property
      have hjN : ((j : Fin (N + 1)) : ℕ) ≤ N := Nat.le_of_lt_succ j.val.isLt
      let Y := fun j => actualAncestorRotatedContour A₀ b W j t
      let u : Fin (N + 1) → ℝ := fun j => ampScale A₀ b j * t
      let φ : Fin (N + 1) → ℝ := fun j => finiteAncestorAngularVelocity A₀ b j * t
      let Gresponse := P.finiteOuterMaterialTubeOfRetardedFamily hR hρ (G t ht) Y u φ (by
        intro l hl i
        rw [hGscale t ht l hl i]
        change (radScale R ρ l • W l t i).val =
          (radScale R ρ l • (exp (((finiteAncestorAngularVelocity A₀ b l * t : ℝ) : ℂ) * I) •
            (rigidRotationGauge (finiteAncestorAngularVelocity A₀ b l) 0 t • W l t i))).val
        rw [smul_smul, exp_undo_rigidRotationGauge, one_smul]) (hQsmall t ht)
      have hAj : ampScale A₀ b j ≠ 0 := (div_pos hA (pow_pos hb j)).ne'
      have htime : physicalTimeFromNormalized (ampScale A₀ b j) 0 (ampScale A₀ b j * t) = t := by
        unfold physicalTimeFromNormalized
        field_simp [hAj]
        <;> simp
      obtain ⟨p, hpder, hpnorm⟩ := hpoint hs hA hb hR hRmax hρ hρ1 hq hqE hsmall houter hc hB hL
        (norm_nonneg _) hCb hD he hd hd16 N j hjN S hS t ⟨ht.1, ht.2.trans hHT⟩ (hglobal t ht)
        (P.finiteOuterMaterialTubeRestrict Gresponse (by omega))
        (P.finiteOuterMaterialTubeRestrict (G t ht) hj) (hinner j hj t ht).1 (hinner j hj t ht).2
        hsepOut hsepIn (hgeom j hj) (W j t) (Qt j t) (V j t) (hW j hj t ht).1
        (hGscale t ht j hj) (hW j hj t ht).2.1 (hW j hj t ht).2.2.1 (hW j hj t ht).2.2.2
        (hx j hj t ht) (hQt j hj t ht) (hV j hj t ht).2 (z j) (hV j hj t ht).1 (hscale j t)
        0 (ampScale A₀ b j * t) htime
      refine ⟨p, fun _ => ⟨?_, ?_⟩⟩
      · have hd := hasDerivAt_same_ancestor_common_clock hγ hγ1 _ p (ampScale A₀ b j) t hpder
        have heq : (fun v =>
          (fun u => rigidRotationGauge (finiteAncestorAngularVelocity A₀ b j / ampScale A₀ b j) 0 u •
            normalizedPhysicalCurve (ampScale A₀ b j) (radScale R ρ j) 0 (z j) u)
            (ampScale A₀ b j * v)) = y j := funext (hphys j)
        simpa only [heq, hphys, y, a] using hd
      · exact hpnorm.trans (finiteRetardedContourResponseBudget_le_baseline_add_feedback
          hCtorus.le hb hsmall houter hL j)
    · exact ⟨0, fun ht' => (ht ht').elim⟩
  choose p hp using hex
  have hzero (j : J) : y j 0 = c₀ j 0 := by
    dsimp only [y, actualAncestorRotatedContour, c₀]
    rw [rigidRotationGauge_entrance, one_smul, hW0 j j.property]
    funext i
    simp [littleCircularMaterialContours]
  have hsmall' : 2 * ((bspeed : ℝ) * H * Real.exp (((bspeed * Kself : ℝ≥0) : ℝ) * H)) * Feedback ≤ 1 := by
    simpa only [bspeed, Feedback, NNReal.coe_mul] using hfeedback
  have hh := delayed_finiteFamily_response_bound hLip a ha hH
    (finiteRetardedSourceBaseline_nonneg hCtorus.le hb hsmall hL he)
    (finiteRetardedAncestorFeedback_nonneg hb houter hB) y c₀ p hzero
    (fun j t ht => (hp j t ht).1)
    (fun j t _ => hasDerivAt_circular_slow_reference hγ hγ1 (ampScale A₀ b j) t)
    (fun j t ht => hyU j j.property t ht)
    (fun j t _ => hcU (ampScale A₀ b j * t))
    (fun j t ht => (hp j t ht).2) hsmall'
  intro j hj t ht
  exact hh ⟨j, hj⟩ t ht

end CircularMaterialTransferProfile
end Euler2D

end
