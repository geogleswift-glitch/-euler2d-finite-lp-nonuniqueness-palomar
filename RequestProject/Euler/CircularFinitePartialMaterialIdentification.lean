module

public import RequestProject.Euler.CircularFiniteActivePrefix
public import RequestProject.Euler.CircularFiniteLabelActiveWindow
public import RequestProject.Euler.CircularFiniteInnerInitialRadius
public import RequestProject.Euler.FinitePhasePartialTorusMaterialIdentification

/-! The actual original-cutoff Euler family is identified with an active
prefix and the actual transported inner label. All localization needed
for material uniqueness follows from the proved cutoff-uniform velocity
bound and a physical scale condition. Deeper contours are not assumed
to remain close to circles. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_finiteEuler_partial_material_identification :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T D c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ D → D ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * D < c → c * R ≤ 1 / 4 →
      ∀ {N k : ℕ} (hk : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ Z : ℝ → FiniteCircularIndex k → ContourC1Space γ,
      Z 0 = (fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (finiteCircularPrefixIndex hk p)).val) →
      (∀ t ∈ Icc (0 : ℝ) D, ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
        ‖contourParameterShiftC1 (β p) (Z t p) - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ <
          finiteCircularInterfaceRadius R ρ p / 4) →
      (∀ p, ContinuousOn (fun t => Z t p) (Icc (0 : ℝ) D)) →
      (∀ t ∈ Icc (0 : ℝ) D, ∀ p θ,
        HasDerivAt (fun u => ContourC1Space.lift γ (Z u p) θ)
          (contourC1BoundaryField (finiteCircularInterfaceStrength A₀ b) (Z t) p θ +
            S.physicalLabelComplexField (P.finiteInnerInitialLabel s A₀ b R ρ N k) t
              (ContourC1Space.lift γ (Z t p) θ)) t) →
      ∀ t ∈ Icc (0 : ℝ) D,
        (∀ p θ, S.forward t (complexTorusPoint (ContourC1Space.lift γ (Z 0 p) θ)) =
          complexTorusPoint (ContourC1Space.lift γ (Z t p) θ)) ∧
        (∀ p, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z 0 p))) =
          complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z t p))) ∧
        (∀ x ∈ torusBox,
          S.transportedScalar (P.finiteActiveInitialLabel s A₀ b R ρ N k) t x =
            phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b) (Z t)
              (centeredComplexHomeomorph.symm x)) ∧
        ∀ x ∈ torusBox,
          S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x =
            phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b) (Z t)
              (centeredComplexHomeomorph.symm x) +
                P.finiteInnerClusterSource s A₀ b R ρ N k S t x := by
  obtain ⟨C, hC, hwindow⟩ := P.exists_uniform_finiteEuler_label_active_window
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T D c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hD hDT hc hcR N k hk S Z hZ0 hphase hZc hmat
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hU : 0 ≤ C * A₀ / (1 - ρ / b) := div_nonneg (mul_nonneg hC.le hA) hden.le
  have hc0 : (5 / 4 : ℝ) < c := lt_of_le_of_lt
    (le_add_of_nonneg_right (mul_nonneg hU hD)) hc
  have hRbox : (5 / 4 : ℝ) * R < 1 := by
    have hh := mul_lt_mul_of_pos_right hc0 hR
    linarith
  obtain ⟨hpoint, hsource⟩ := hwindow hs hA hb hR hRmax hρ hρ1 hρb hq hqE
    hD hDT hc (by linarith : c * R < 1) N S
  have hlabelzero (j : ℕ) {x : R2} (hx : (5 / 4 : ℝ) * R < ‖x‖) :
      P.finitePlanarLabel s A₀ b R ρ N j x = 0 := by
    have hr : radScale R ρ j ≤ R :=
      mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
    exact P.finitePlanarLabel_eq_zero_of_radius hs hR hρ N j
      ((mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 5 / 4)).trans_lt hx)
  let w : R2 → ℝ := fun x => P.finiteActivePlanarLabel s A₀ b R ρ N k (x - torusCenter)
  have hwzero {x : R2} (hx : (5 / 4 : ℝ) * R < ‖x - torusCenter‖) : w x = 0 := by
    exact Finset.sum_eq_zero fun j _ => hlabelzero j hx
  have hinnerzero : ∀ y ∈ torusBox, (5 / 4 : ℝ) * R < ‖y - torusCenter‖ →
      P.finiteInnerInitialLabel s A₀ b R ρ N k y = 0 := by
    intro y hy hn
    apply Finset.sum_eq_zero
    intro j _
    change periodicCenteredSource (P.finitePlanarLabel s A₀ b R ρ N j) y = 0
    rw [periodicCenteredSource_eq_on_box
      (P.finitePlanarLabel_zero_of_one_le_norm hs hR hRmax hρ hρ1 N j) hy]
    exact hlabelzero j hn
  have hinnersource := hsource (P.finiteInnerInitialLabel s A₀ b R ρ N k) hinnerzero
  have hωeq (x : R2) : phaseFiniteContourPatchVorticity
      (finiteCircularInterfaceStrength A₀ b) (Z 0) (centeredComplexHomeomorph.symm x) = w x := by
    rw [hZ0, P.finiteCircularPrefix_initial_density_eq hR hρ hk,
      centeredComplexHomeomorph_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  let A : Set R2 := closedBall torusCenter ((5 / 4) * R)
  have hAbox : A ⊆ torusBox := by
    intro x hx
    exact norm_sub_center_lt_one_mem_box ((mem_closedBall_iff_norm.mp hx).trans_lt hRbox)
  have hdomain (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (p : FiniteCircularIndex k) {z : ℂ}
      (hz : z ∈ contourRadialFill (ContourC1Space.lift γ (Z t p))) : complexTorusPoint z ∈ A := by
    obtain ⟨β, hβ⟩ := hphase t ht
    apply mem_closedBall_iff_norm.mpr
    rw [complexTorusPoint_sub_center_norm]
    have hn := norm_lt_of_mem_contourRadialFill_of_shift (Z t p)
      (finiteCircularReferenceC1 hγ hγ1 R ρ p) (finiteCircularInterfaceRadius_pos hR hρ p)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ p) (β p) (hβ p).le hz
    have hr := finiteCircularInterfaceRadius_le hR hρ hρ1 p
    linarith
  have hboundary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (p : FiniteCircularIndex k) (θ : ℝ) :
      complexTorusPoint (ContourC1Space.lift γ (Z t p) θ) ∈ A := by
    obtain ⟨β, hβ⟩ := hphase t ht
    have hn := finiteCircular_contour_boundary_radius hγ hγ1 hR hρ hρ1
      (fun j => contourParameterShiftC1 (β j) (Z t j)) (fun j => (hβ j).le) p (θ - β p)
    apply mem_closedBall_iff_norm.mpr
    simpa only [lift_contourParameterShiftC1, sub_add_cancel] using hn
  have htri (u v : R2) : ‖u - v‖ ≤ ‖u - torusCenter‖ + ‖v - torusCenter‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (u - torusCenter) (v - torusCenter)
  obtain ⟨hqlp, hqper, hqbound⟩ := P.finiteInnerInitialLabel_bounds hs hA hb hR hRmax hρ hρ1 N k
  have hagree := S.finitePhase_partial_actual_agreement (finiteCircularInterfaceStrength A₀ b)
    Z (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
    (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
    (P.finiteInnerInitialLabel s A₀ b R ρ N k) hqlp hqper hqbound hD hDT hZc hphase hmat w
    (fun x => (hωeq x).symm)
    (P.finiteCircularPrefix_initial_decomposition hs hR hRmax hρ hρ1 hq hqE hk)
    hAbox (fun p z hz => hdomain 0 ⟨le_rfl, hD⟩ p hz) (hboundary 0 ⟨le_rfl, hD⟩)
    (by
      intro t ht a ha
      exact ae_of_all _ fun y hy => by
        have hy0 : ‖y - torusCenter‖ ≤ (5 / 4 : ℝ) * R := by
          apply le_of_not_gt
          intro hn
          exact hy (hwzero hn)
        have hh := htri (S.forward t a) (S.forward t y)
        have ha' := hpoint t ht a (mem_closedBall_iff_norm.mp ha)
        have hy' := hpoint t ht y hy0
        linarith)
    (by
      intro t ht a ha
      filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hybox
      intro hy
      have hyn : ‖y - torusCenter‖ ≤ c * R := by
        apply le_of_not_gt
        intro hn
        exact hy (hinnersource t ht y hybox hn)
      have hh := htri (S.forward t a) y
      have ha' := hpoint t ht a (mem_closedBall_iff_norm.mp ha)
      linarith)
  intro t ht
  have hactive : ∀ x ∈ torusBox,
      S.transportedScalar (P.finiteActiveInitialLabel s A₀ b R ρ N k) t x =
        phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b) (Z t)
          (centeredComplexHomeomorph.symm x) := by
    intro x hx
    apply S.transportedScalar_finitePhase_eq_of_domain_images
      (finiteCircularInterfaceStrength A₀ b) (Z 0) (Z t) _
      (fun y hy => (P.finiteActiveInitialLabel_eq_on_box hs hR hRmax hρ hρ1 N k hy).trans
        (hωeq y).symm) t ⟨ht.1, ht.2.trans hDT⟩
      (fun p y hy => by
        obtain ⟨z, hz, rfl⟩ := hy
        exact hAbox (hdomain 0 ⟨le_rfl, hD⟩ p hz))
      (fun p y hy => by
        obtain ⟨z, hz, rfl⟩ := hy
        exact hAbox (hdomain t ht p hz)) (hagree t ht).2 hx
  refine ⟨(hagree t ht).1, (hagree t ht).2, hactive, ?_⟩
  intro x hx
  calc
    _ = S.transportedScalar (P.finiteActiveInitialLabel s A₀ b R ρ N k) t x +
        S.transportedScalar (P.finiteInnerInitialLabel s A₀ b R ρ N k) t x :=
      (P.finiteActiveInitialLabel_add_inner hs hR hRmax hρ hρ1 hk _).symm
    _ = _ := by rw [hactive x hx]; rfl

end CircularMaterialTransferProfile
end Euler2D

end
