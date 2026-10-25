module

public import RequestProject.Euler.CircularFinitePrefixCanonicalStart
public import RequestProject.Euler.CircularFinitePrefixCanonicalUniqueness
public import RequestProject.Euler.CircularFinitePrefixBufferContinuation
public import RequestProject.Euler.EulerLabelParticleRadiusSupport

/-! Actual active-prefix evolution up to a target event or a prescribed
horizon. Only the provisional geometric improvement is left to the
capture estimates: local existence, overlap uniqueness, raw source
validity at the endpoint, and continuation are constructed here from
the original finite Euler solution. -/

@[expose] public section

set_option maxHeartbeats 7000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) prefixEventLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) prefixEventLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) prefixEventC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) prefixEventC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualPrefix_trajectory_or_event :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hcap Hglob a ai₀ ai η c : ℝ},
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
      ∀ {N k : ℕ} (hk : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ t ∈ Icc (0 : ℝ) Hglob, ∀ x ∈ torusBox,
        a < ‖x - torusCenter‖ →
          S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0) →
      (∀ p : FiniteCircularIndex k, 32 * ai ≤ finiteCircularInterfaceRadius R ρ p) →
      let qinner := P.finiteInnerInitialLabel s A₀ b R ρ N k
      let F : ℝ → (FiniteCircularIndex k → LittleContourSpace γ) →
          FiniteCircularIndex k → LittleContourSpace γ := S.actualPartialPhaseField qinner hγ hγ1
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceStrength A₀ b)
      let U : ℝ → Set (FiniteCircularIndex k → LittleContourSpace γ) := S.actualPartialPhaseDomain qinner
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob
      let Zinit : FiniteCircularIndex k → LittleContourSpace γ := fun p =>
        finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hk p)
      ∀ event : ℝ → (FiniteCircularIndex k → LittleContourSpace γ) → Prop,
      (∀ D, 0 < D → D ≤ Hcap → ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        IsBanachTimeDomainTrajectoryOn F U Zinit D X →
        (∀ t ∈ Icc (0 : ℝ) D, ¬ event t (X t)) →
        ∀ t ∈ Icc (0 : ℝ) D,
          (∃ β : FiniteCircularIndex k → ℝ, ∀ p,
            ‖contourParameterShiftC1 (β p) (X t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
              η * radScale R ρ p.1) ∧
          ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
            ‖S.forward t y - torusCenter‖ ≤ ai₀) →
      (∃ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        IsBanachTimeDomainTrajectoryOn F U Zinit Hcap X) ∨
      ∃ t ∈ Icc (0 : ℝ) Hcap, ∃ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        IsBanachTimeDomainTrajectoryOn F U Zinit t X ∧ event t (X t) := by
  obtain ⟨C, hC, hUnique⟩ := P.exists_uniform_actualPrefix_canonical_uniqueness
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hcap Hglob a ai₀ ai η c _ hs hA hb hR hRmax hρ hρ128 hρb hq hqE
    hH hHglob hglobT hc hcR hRa ha16 hai₀ hbuffer hai1 hη hηa hηgap hsize hancient N k hk S hS hglobal hsep
  dsimp only
  intro event hbootstrap
  let qinner := P.finiteInnerInitialLabel s A₀ b R ρ N k
  let F : ℝ → (FiniteCircularIndex k → LittleContourSpace γ) →
      FiniteCircularIndex k → LittleContourSpace γ := S.actualPartialPhaseField qinner hγ hγ1
    (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
    (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
    (finiteCircularInterfaceStrength A₀ b)
  let U : ℝ → Set (FiniteCircularIndex k → LittleContourSpace γ) := S.actualPartialPhaseDomain qinner
    (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob
  let Zinit : FiniteCircularIndex k → LittleContourSpace γ := fun p =>
    finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hk p)
  change (∃ X, IsBanachTimeDomainTrajectoryOn F U Zinit Hcap X) ∨
    ∃ t ∈ Icc (0 : ℝ) Hcap, ∃ X, IsBanachTimeDomainTrajectoryOn F U Zinit t X ∧ event t (X t)
  have hρ1 : ρ ≤ 1 := by linarith only [hρ128, cellA_lt_one]
  have hρa : ρ ≤ cellA / 4 := by linarith only [hρ128, cellA_pos]
  have ha : 0 < a := (by positivity : 0 < (5 / 4 : ℝ) * R).trans hRa
  have hstart : ∃ D > 0, D ≤ Hcap ∧ ∃ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      IsBanachTimeDomainTrajectoryOn F U Zinit D X := by
    obtain ⟨δ, hδ, _hδT, Z, hZ0, hZc, hZd, hZm, hZmat⟩ :=
      P.exists_actualPrefix_canonical_local_start hs hA hb hR hRmax hρ hρ128 hq hqE
        ((hH.trans hHglob).trans_le hglobT) hRa ha16 hη hηa hηgap hsize hancient hk S hS
    let D := min δ Hcap
    have hDδ : D ≤ δ := min_le_left _ _
    refine ⟨D, lt_min hδ hH, min_le_right _ _, Z, hZ0, ?_, ?_, ?_⟩
    · exact hZc.mono (fun t ht => ⟨ht.1, ht.2.trans hDδ⟩)
    · exact fun t ht => hZd t ⟨ht.1, ht.2.trans hDδ⟩
    · intro t ht
      have htδ : t ∈ Icc (0 : ℝ) δ := ⟨ht.1, ht.2.trans hDδ⟩
      refine ⟨⟨ht.1, (ht.2.trans (min_le_right _ _)).trans hHglob.le⟩,
        (hZm t htδ).1, (hZm t htδ).2.1, (hZm t htδ).2.2, ?_⟩
      exact (S.actualPartialPhaseField_material_iff hγ hγ1
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceStrength A₀ b) (hZd t htδ) (hZm t htδ).1).mp (hZmat t htδ)
  apply exists_banachTimeDomainTrajectory_or_event F U Zinit Hcap event hstart
    (hUnique hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR hk S)
  intro D hD hDH α hα0 hαd hαmem hnoevent
  have hDglob : D < Hglob := hDH.trans_lt hHglob
  have hest (t : ℝ) (ht : t ∈ Ico (0 : ℝ) D) :
      (∃ β : FiniteCircularIndex k → ℝ, ∀ p,
        ‖contourParameterShiftC1 (β p) (α t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1) ∧
      ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t y - torusCenter‖ ≤ ai₀ := by
    let B := (t + D) / 2
    have hB : 0 < B := by dsimp only [B]; linarith only [ht.1, hD]
    have hBD : B < D := by dsimp only [B]; linarith only [ht.2]
    have htB : t ≤ B := by dsimp only [B]; linarith only [ht.2]
    have hpath : IsBanachTimeDomainTrajectoryOn F U Zinit B α := by
      refine ⟨hα0, ?_, ?_, ?_⟩
      · exact fun s hs => (hαd s ⟨hs.1, hs.2.trans_lt hBD⟩).continuousAt.continuousWithinAt
      · exact fun s hs => hαd s ⟨hs.1, hs.2.trans_lt hBD⟩
      · exact fun s hs => hαmem s ⟨hs.1, hs.2.trans_lt hBD⟩
    exact hbootstrap B hB (hBD.le.trans hDH) α hpath
      (fun s hs => hnoevent s ⟨hs.1, hs.2.trans_lt hBD⟩) t ⟨ht.1, htB⟩
  have hparticles := S.particle_radius_closed_of_prebound hD (fun t ht => (hest t ht).2)
  have hqinitial : ∀ x ∈ torusBox,
      x ∉ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k → qinner x = 0 := by
    intro x hx hn
    apply Finset.sum_eq_zero
    intro j hj
    by_contra hne
    exact hn ⟨hx, j, hj, hne⟩
  have hpast : ∀ t ∈ Icc (0 : ℝ) D, ∀ x ∈ torusBox,
      ai₀ < ‖x - torusCenter‖ → P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0 := by
    intro t ht
    exact S.transportedScalar_support_of_particle_radius
      ⟨ht.1, ht.2.trans (hDglob.le.trans hglobT)⟩ (hbuffer.trans hai1)
      (fun _ hx => hx.1) hqinitial (hparticles t ht)
  obtain ⟨δ, hδ, _hδone, hδglob, _hinner, Y, hYα, hYc, hYd, hYm, hYmat⟩ :=
    P.exists_actualPrefix_continuation_of_particle_buffer hs hA hb hR hRmax hρ hρ1 hq hqE
      hglobT hD hDglob (show (0 : ℝ) < 1 by norm_num) ha ha16 hai₀ hbuffer hai1
      hη hηa hηgap hρa hsize N k hk S hS hglobal
      (hparticles D ⟨hD.le, le_rfl⟩) hpast hsep α hαd
      (fun t ht => ⟨(hαmem t ht).2.1, (hαmem t ht).2.2.1, (hαmem t ht).2.2.2.1⟩)
      (fun t ht => (hest t ⟨ht.1.le, ht.2⟩).1)
  refine ⟨δ, hδ, Y, (hYα 0 ⟨le_rfl, hD⟩).trans hα0, hYc, hYd, ?_⟩
  intro t ht
  refine ⟨⟨ht.1, ht.2.trans hδglob⟩,
    (hYm t ht).1, (hYm t ht).2.1, (hYm t ht).2.2, ?_⟩
  exact (S.actualPartialPhaseField_material_iff hγ hγ1
    (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
    (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
    (finiteCircularInterfaceStrength A₀ b) (hYd t ht) (hYm t ht).1).mp (hYmat t ht)

end CircularMaterialTransferProfile
end Euler2D

end
