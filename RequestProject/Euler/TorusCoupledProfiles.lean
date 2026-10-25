module

public import RequestProject.Euler.TorusKernelTranslation
public import RequestProject.Euler.TorusKernelConvolution
public import RequestProject.Euler.CoupledKernelSplit

/-! Actual periodized near and annular profiles for nonlinear torus
particle coupling. Two close arguments share the same supported
coordinate formula even when their chosen representatives cross
the boundary of the fundamental square. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real

namespace Euler2D

theorem isTorusPeriodic_periodicCenteredSource (q : R2 → ℝ) : IsTorusPeriodic (periodicCenteredSource q) :=
  isTorusPeriodic_torusPeriodize _

theorem isTorusPeriodic_comp_sub_left {F : Type*} {f : R2 → F}
    (hf : IsTorusPeriodic f) (a : R2) : IsTorusPeriodic (fun x => f (a - x)) := by
  intro x i
  have hh := hf (a - (x + EuclideanSpace.single i (2 * Real.pi))) i
  have he : a - (x + EuclideanSpace.single i (2 * Real.pi)) +
      EuclideanSpace.single i (2 * Real.pi) = a - x := by abel
  rw [he] at hh
  exact hh.symm

theorem isTorusPeriodic_comp_add_right {F : Type*} {f : R2 → F}
    (hf : IsTorusPeriodic f) (h : R2) : IsTorusPeriodic (fun x => f (x + h)) := by
  intro x i
  have he : x + EuclideanSpace.single i (2 * Real.pi) + h =
      (x + h) + EuclideanSpace.single i (2 * Real.pi) := by abel
  exact (congrArg f he).trans (hf _ i)

theorem periodicCenteredSource_eq_wrapped {q : R2 → ℝ}
    (hq : ∀ x, 1 ≤ ‖x‖ → q x = 0) (x : R2) :
    periodicCenteredSource q x = q (torusWrap x - torusCenter) := by
  rw [← (isTorusPeriodic_periodicCenteredSource q).eq_torusWrap x]
  exact periodicCenteredSource_eq_on_box hq (torusRep_mem _)

theorem periodicCenteredSource_add_eq_on_box {q : R2 → ℝ}
    (hq : ∀ x, 1 ≤ ‖x‖ → q x = 0) {x h : R2}
    (hx : x ∈ torusBox) (hh : ‖h‖ ≤ 1 / 2) :
    periodicCenteredSource q (x + h) = q (x + h - torusCenter) := by
  have hz (k : Fin 2 → ℤ) (hk : k ≠ 0) : q (x + h + torusLatticeShift k - torusCenter) = 0 := by
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hk (funext hn)
    have hhi : -(1 / 2 : ℝ) ≤ h i ∧ h i ≤ 1 / 2 := abs_le.mp ((abs_coord_le h i).trans hh)
    have hcoord : (1 : ℝ) ≤ |(x + h + torusLatticeShift k - torusCenter) i| := by
      have hxi := hx i
      have hsplit : k i ≤ -1 ∨ 1 ≤ k i := by omega
      rcases hsplit with hki | hki
      · have hki' : (k i : ℝ) ≤ -1 := by exact_mod_cast hki
        have hs : 2 * π * (k i : ℝ) ≤ -2 * π := by nlinarith [pi_pos]
        simp only [PiLp.sub_apply, PiLp.add_apply, torusLatticeShift_apply, torusCenter_apply]
        rw [abs_of_nonpos (by linarith [pi_gt_three, hhi.2, hxi.2])]
        linarith [pi_gt_three, hhi.2, hxi.2]
      · have hki' : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hki
        have hs : 2 * π ≤ 2 * π * (k i : ℝ) := by nlinarith [pi_pos]
        simp only [PiLp.sub_apply, PiLp.add_apply, torusLatticeShift_apply, torusCenter_apply]
        rw [abs_of_nonneg (by linarith [pi_gt_three, hhi.1, hxi.1])]
        linarith [pi_gt_three, hhi.1, hxi.1]
    exact hq _ (hcoord.trans (abs_coord_le _ i))
  change (∑' k, q (x + h + torusLatticeShift k - torusCenter)) = _
  rw [tsum_eq_single 0 hz, torusLatticeShift_zero, add_zero]

theorem periodicCenteredSource_common_chart {q : R2 → ℝ}
    (hq : ∀ x, 1 ≤ ‖x‖ → q x = 0) (a b : R2) (hab : ‖b - a‖ ≤ 1 / 2) :
    periodicCenteredSource q b = q (torusWrap a + (b - a) - torusCenter) := by
  have hp := isTorusPeriodic_comp_add_right (isTorusPeriodic_periodicCenteredSource q) (b - a)
  have he := hp.eq_torusWrap a
  change periodicCenteredSource q (torusWrap a + (b - a)) = periodicCenteredSource q (a + (b - a)) at he
  rw [show a + (b - a) = b by abel] at he
  rw [← he]
  exact periodicCenteredSource_add_eq_on_box hq (torusRep_mem _) hab

theorem integrable_periodicCenteredSource {q : R2 → ℝ} (hq : Integrable q)
    (hzero : ∀ x, 1 ≤ ‖x‖ → q x = 0) : Integrable (periodicCenteredSource q) μT := by
  apply ((hq.comp_sub_right torusCenter).integrableOn).congr
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  exact (periodicCenteredSource_eq_on_box hzero hx).symm

theorem integrable_periodicCenteredSource_material {q : R2 → ℝ} (hq : Integrable q)
    (hzero : ∀ x, 1 ≤ ‖x‖ → q x = 0) {X : R2 → R2} (hX : TorusAreaPreserving X) (x : R2) :
    Integrable (fun b => periodicCenteredSource q ((x + torusCenter) - X b)) μT := by
  have hp := isTorusPeriodic_periodicCenteredSource q
  have hg := (torusAreaPreserving_sub_left (x + torusCenter)).integrable_comp
    (integrable_periodicCenteredSource hq hzero) hp
  have hh := hX.integrable_comp hg (isTorusPeriodic_comp_sub_left hp _)
  exact hh

theorem integral_periodicCenteredSource_material {q : R2 → ℝ} (hq : Integrable q)
    (hzero : ∀ x, 1 ≤ ‖x‖ → q x = 0) {X : R2 → R2} (hX : TorusAreaPreserving X) (x : R2) :
    (∫ b in torusBox, periodicCenteredSource q ((x + torusCenter) - X b)) = ∫ z, q z := by
  have hp := isTorusPeriodic_periodicCenteredSource q
  have hi := integrable_periodicCenteredSource hq hzero
  have hg := (torusAreaPreserving_sub_left (x + torusCenter)).integrable_comp hi hp
  calc
    _ = ∫ b in torusBox, periodicCenteredSource q ((x + torusCenter) - b) :=
      hX.integral_comp hg.aestronglyMeasurable (isTorusPeriodic_comp_sub_left hp _)
    _ = ∫ b in torusBox, periodicCenteredSource q b :=
      (torusAreaPreserving_sub_left (x + torusCenter)).integral_comp hi.aestronglyMeasurable hp
    _ = _ := integral_periodicCenteredSource hzero

end Euler2D

end
