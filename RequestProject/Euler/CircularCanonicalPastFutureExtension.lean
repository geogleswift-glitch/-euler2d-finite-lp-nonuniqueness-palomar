module

public import RequestProject.Euler.CircularFinitePrefixEventContinuation
public import RequestProject.Euler.CircularDeepestCaptureInitialState

/-! Continue a genuine active prefix from a true past state on the SAME
Euler system. Actual material uniqueness identifies every provisional
prefix on its overlap with the supplied past. The future estimates are
used only after this identification. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower

theorem canonicalPrefixAlignedCurrentCell_zero_congr {γ : ℝ≥0}
    (A₀ b R ρ : ℝ) (k : ℕ) (entrance : ℝ)
    {X Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ}
    (hXY : X entrance = Y entrance) :
    canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X 0 =
      canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Y 0 := by
  unfold canonicalPrefixAlignedCurrentCell canonicalPrefixAbsoluteCell
    normalizedPhysicalCurve physicalTimeFromNormalized
  simp only [zero_div, add_zero, hXY]

theorem canonicalPrefixStageDeviation_zero_congr {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (A₀ b R ρ : ℝ) (k : ℕ) (entrance : ℝ)
    {X Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ}
    (hXY : X entrance = Y entrance) :
    canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X 0 =
      canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y 0 := by
  funext j
  unfold canonicalPrefixStageDeviation canonicalPrefixAbsoluteFamily
  split_ifs with hj
  · unfold canonicalPrefixAbsoluteCell normalizedPhysicalCurve physicalTimeFromNormalized
    simp only [zero_div, add_zero, hXY]
  · rfl

theorem canonicalPrefix_capture_particle_buffer {R ρ Cb D : ℝ}
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hCb : 0 ≤ Cb) (hD : 0 ≤ D)
    (hsmall : Cb * ρ * (1 + D) ≤ cellA / 128) (k : ℕ) :
    let ai₀ := Cb * ρ * radScale R ρ k * (1 + D)
    let ai := cellA * radScale R ρ k / 64
    0 ≤ ai₀ ∧ ai₀ < ai ∧ ai < 1 ∧
      ∀ p : FiniteCircularIndex k, 32 * ai ≤ finiteCircularInterfaceRadius R ρ p := by
  dsimp only
  have hrk : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hrkR : radScale R ρ k ≤ R :=
    mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hprod : cellA * radScale R ρ k ≤ R :=
    (mul_le_of_le_one_left hrk.le cellA_lt_one.le).trans hrkR
  have hsmallR := mul_le_mul_of_nonneg_right hsmall hrk.le
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · nlinarith only [hsmallR, mul_pos cellA_pos hrk]
  · nlinarith only [hprod, hRmax]
  · intro p
    have hrp : 0 < radScale R ρ p.1 := radScale_pos hR hρ p.1
    have hrkp : radScale R ρ k ≤ radScale R ρ p.1 := by
      by_cases hj : (p.1 : ℕ) = k
      · rw [hj]
      · have hjk : (p.1 : ℕ) < k := by have hp := p.1.isLt; omega
        exact (radScale_le_ratio_of_lt hR hρ hρ1 hjk).trans
          (mul_le_of_le_one_left hrp.le hρ1)
    have h₁ := mul_le_mul_of_nonneg_left hrkp cellA_pos.le
    have h₂ := mul_le_mul_of_nonneg_left (circularContourRadii_bounds p.2).2.1 hrp.le
    change 32 * (cellA * radScale R ρ k / 64) ≤
      radScale R ρ p.1 * circularContourRadii p.2
    nlinarith only [h₁, h₂, mul_pos cellA_pos hrk]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualPrefix_past_future_extension :
    ∃ C > 0, ∀ {s A₀ b R ρ q T Hcap Hglob a ai₀ ai η c entrance : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ128 : ρ ≤ cellA / 128)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 < Hcap → Hcap < Hglob → Hglob ≤ T →
      5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      (5 / 4) * R < a → a ≤ 1 / 16 →
      0 ≤ ai₀ → ai₀ < ai → ai < 1 →
      0 ≤ η → η ≤ cellA / 16 → η ≤ (1 - cellA) / 16 →
      R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      0 ≤ entrance → entrance ≤ Hcap →
      ∀ {N k : ℕ} (hk : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ t ∈ Icc (0 : ℝ) Hglob, ∀ x ∈ torusBox, a < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0) →
      (∀ p : FiniteCircularIndex k, 32 * ai ≤ finiteCircularInterfaceRadius R ρ p) →
      ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hk S entrance Y →
      (∀ t ∈ Icc (0 : ℝ) entrance,
        ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
          ‖contourParameterShiftC1 (β p) (Y t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
            η * radScale R ρ p.1) →
      (∀ t ∈ Icc (0 : ℝ) entrance, ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t y - torusCenter‖ ≤ ai₀) →
      (∀ D, entrance < D → D ≤ Hcap →
        ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hk S D X →
        EqOn X Y (Icc (0 : ℝ) entrance) →
        ∀ t ∈ Icc entrance D,
          (∃ β : FiniteCircularIndex k → ℝ, ∀ p,
            ‖contourParameterShiftC1 (β p) (X t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
              η * radScale R ρ p.1) ∧
          ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
            ‖S.forward t y - torusCenter‖ ≤ ai₀) →
      ∃ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hk S Hcap X ∧
        EqOn X Y (Icc (0 : ℝ) entrance) := by
  obtain ⟨Ce, hCe, hextend⟩ := P.exists_uniform_actualPrefix_trajectory_or_event
  obtain ⟨Cu, hCu, hunique⟩ := P.exists_uniform_actualPrefix_canonical_uniqueness
  let C := max Ce Cu
  refine ⟨C, hCe.trans_le (le_max_left _ _), ?_⟩
  intro s A₀ b R ρ q T Hcap Hglob a ai₀ ai η c entrance _ hs hA hb hR hRmax hρ hρ128
    hρb hq hqE hHcap hHHglob hglobT hdrift hcR hRa ha16 hai₀ hbuffer hai1
    hη hηa hηgap hsize hancient he heH N k hk S hS hglobal hsep Y hY hpast hparticles hfuture
  have hρ1 : ρ ≤ 1 := by linarith only [hρ128, cellA_lt_one]
  have hHglob : 0 ≤ Hglob := (hHcap.trans hHHglob).le
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ C) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < c :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA) hden.le) hHglob)).trans_lt hdrift
  have heq (D : ℝ) (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
      (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hk S D X) :=
    hunique hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT
      (hdriftFor Cu (le_max_right _ _)) hcR hk S hX hY
  have hexists := hextend hs hA hb hR hRmax hρ hρ128 hρb hq hqE hHcap hHHglob hglobT
    (hdriftFor Ce (le_max_left _ _)) hcR hRa ha16 hai₀ hbuffer hai1 hη hηa hηgap
    hsize hancient hk S hS hglobal hsep
  dsimp only at hexists
  have hpath := hexists (fun _ _ => False) (by
    intro D hD hDH X hX _ t ht
    by_cases hte : t ≤ entrance
    · have hXY : X t = Y t := heq D X hX ⟨ht.1, le_min ht.2 hte⟩
      exact ⟨by simpa only [hXY] using hpast t ⟨ht.1, hte⟩,
        hparticles t ⟨ht.1, hte⟩⟩
    · have heD : entrance < D := (lt_of_not_ge hte).trans_le ht.2
      have hXY : EqOn X Y (Icc (0 : ℝ) entrance) := by
        intro u hu
        exact heq D X hX ⟨hu.1, le_min (hu.2.trans heD.le) hu.2⟩
      exact hfuture D heD hDH X hX hXY t ⟨(lt_of_not_ge hte).le, ht.2⟩)
  rcases hpath with ⟨X, hX⟩ | ⟨t, ht, X, hX, hf⟩
  · refine ⟨X, hX, ?_⟩
    intro t ht
    exact heq Hcap X hX ⟨ht.1, le_min (ht.2.trans heH) ht.2⟩
  · exact False.elim hf

end CircularMaterialTransferProfile
end Euler2D

end
