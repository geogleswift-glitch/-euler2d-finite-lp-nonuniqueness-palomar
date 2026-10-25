module

public import RequestProject.Euler.RadialStationary

/-!
# Actual smooth periodization of an interior coordinate test

The lattice sum is locally a finite sum. A test vanishing outside the
unit disk about the torus center therefore has a globally smooth periodic
extension which agrees with it on the original fundamental square.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

def torusLatticeShift (k : Fin 2 → ℤ) : R2 :=
  WithLp.toLp 2 (fun i => (2 * Real.pi) * (k i : ℝ))

@[simp] lemma torusLatticeShift_apply (k : Fin 2 → ℤ) (i : Fin 2) :
    torusLatticeShift k i = (2 * Real.pi) * (k i : ℝ) := rfl

@[simp] lemma torusLatticeShift_zero : torusLatticeShift 0 = 0 := by
  ext i
  simp [torusLatticeShift]

lemma torusLatticeShift_add (k l : Fin 2 → ℤ) :
    torusLatticeShift (k + l) = torusLatticeShift k + torusLatticeShift l := by
  ext i
  simp [torusLatticeShift, mul_add]

lemma torusLatticeShift_single (i : Fin 2) :
    torusLatticeShift (Pi.single i (1 : ℤ)) = EuclideanSpace.single i (2 * Real.pi) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [torusLatticeShift, EuclideanSpace.single_apply]
  · simp [torusLatticeShift, EuclideanSpace.single_apply, h]

def torusPeriodize {F : Type*} [NormedAddCommGroup F] (f : R2 → F) (x : R2) : F :=
  ∑' k : Fin 2 → ℤ, f (x + torusLatticeShift k)

theorem isTorusPeriodic_torusPeriodize {F : Type*} [NormedAddCommGroup F] (f : R2 → F) :
    IsTorusPeriodic (torusPeriodize f) := by
  intro x i
  let e : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) := Equiv.addRight (Pi.single i (1 : ℤ))
  calc
    torusPeriodize f (x + EuclideanSpace.single i (2 * Real.pi)) =
        ∑' k, f (x + torusLatticeShift (e k)) := by
      apply tsum_congr
      intro k
      congr 1
      change x + EuclideanSpace.single i (2 * Real.pi) + torusLatticeShift k =
        x + torusLatticeShift (k + Pi.single i (1 : ℤ))
      rw [torusLatticeShift_add, torusLatticeShift_single]
      abel
    _ = torusPeriodize f x := e.tsum_eq (fun k => f (x + torusLatticeShift k))

lemma periodize_local_index_bound {F : Type*} [NormedAddCommGroup F] {f : R2 → F}
    (hzero : ∀ y, 1 ≤ ‖y - torusCenter‖ → f y = 0) (x : R2) :
    ∃ N : ℕ, ∀ y ∈ ball x 1, ∀ k : Fin 2 → ℤ,
      f (y + torusLatticeShift k) ≠ 0 →
        k ∈ Finset.Icc (fun _ => -(N : ℤ)) (fun _ => (N : ℤ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ + Real.pi + 2)
  refine ⟨N, ?_⟩
  intro y hy k hk
  have hraw : ‖y + torusLatticeShift k - torusCenter‖ < 1 := by
    by_contra hn
    exact hk (hzero _ (le_of_not_gt hn))
  have hy' : ‖y - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hy
  have hki (i : Fin 2) : |(k i : ℝ)| < (N : ℝ) := by
    have h0 : |(y + torusLatticeShift k - torusCenter) i| < 1 :=
      (abs_coord_le _ i).trans_lt hraw
    have h1 : |(y - x) i| < 1 := (abs_coord_le _ i).trans_lt hy'
    have hx : |x i| ≤ ‖x‖ := abs_coord_le x i
    have hb : |(2 * Real.pi) * (k i : ℝ)| < ‖x‖ + Real.pi + 2 := by
      rw [abs_lt] at h0 h1 ⊢
      rw [abs_le] at hx
      simp only [PiLp.sub_apply, PiLp.add_apply, torusLatticeShift_apply, torusCenter_apply] at h0 h1
      constructor <;> linarith [Real.pi_pos]
    have hle : |(k i : ℝ)| ≤ |(2 * Real.pi) * (k i : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [abs_nonneg (k i : ℝ), Real.pi_gt_three]
    exact hle.trans_lt (hb.trans hN)
  rw [Finset.mem_Icc]
  constructor <;> intro i
  · have h := (abs_lt.mp (hki i)).1.le
    exact_mod_cast h
  · have h := (abs_lt.mp (hki i)).2.le
    exact_mod_cast h

theorem contDiff_torusPeriodize {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : R2 → F} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ y, 1 ≤ ‖y - torusCenter‖ → f y = 0) :
    ContDiff ℝ ∞ (torusPeriodize f) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨N, hN⟩ := periodize_local_index_bound hzero x
  let K := Finset.Icc (fun _ : Fin 2 => -(N : ℤ)) (fun _ => (N : ℤ))
  have heq : torusPeriodize f =ᶠ[𝓝 x] fun y => ∑ k ∈ K, f (y + torusLatticeShift k) := by
    filter_upwards [ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    apply tsum_eq_sum
    intro k hk
    by_contra hn
    exact hk (hN y hy k hn)
  have hsmooth : ContDiff ℝ ∞ (fun y => ∑ k ∈ K, f (y + torusLatticeShift k)) := by
    apply ContDiff.sum
    intro k hk
    exact hf.comp (contDiff_id.add contDiff_const)
  exact hsmooth.contDiffAt.congr_of_eventuallyEq heq

lemma torusPeriodize_eq_on_box {F : Type*} [NormedAddCommGroup F] {f : R2 → F}
    (hzero : ∀ y, 1 ≤ ‖y - torusCenter‖ → f y = 0) {x : R2} (hx : x ∈ torusBox) :
    torusPeriodize f x = f x := by
  have hz : ∀ k : Fin 2 → ℤ, k ≠ 0 → f (x + torusLatticeShift k) = 0 := by
    intro k hk
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hk (funext hn)
    have hki : k i ≤ -1 ∨ 1 ≤ k i := by omega
    have hcoord : Real.pi ≤ |(x + torusLatticeShift k - torusCenter) i| := by
      have hxi := hx i
      simp only [PiLp.sub_apply, PiLp.add_apply, torusLatticeShift_apply, torusCenter_apply]
      rcases hki with hki | hki
      · have hi' : (k i : ℝ) ≤ -1 := by exact_mod_cast hki
        have hs : (2 * Real.pi) * (k i : ℝ) ≤ -2 * Real.pi := by nlinarith [Real.pi_pos]
        have hval : x i + (2 * Real.pi) * (k i : ℝ) - Real.pi ≤ -Real.pi := by linarith [hxi.2]
        rw [abs_of_nonpos (by linarith [Real.pi_pos])]
        linarith
      · have hi' : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hki
        have hs : 2 * Real.pi ≤ (2 * Real.pi) * (k i : ℝ) := by nlinarith [Real.pi_pos]
        have hval : Real.pi ≤ x i + (2 * Real.pi) * (k i : ℝ) - Real.pi := by linarith [hxi.1]
        rw [abs_of_nonneg (by linarith [Real.pi_pos])]
        exact hval
    apply hzero
    exact (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi).trans
      (hcoord.trans (abs_coord_le _ i))
  change (∑' k, f (x + torusLatticeShift k)) = _
  rw [tsum_eq_single 0 hz, torusLatticeShift_zero, add_zero]

theorem isScalarTest_torusPeriodize {f : R2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ y, 1 ≤ ‖y - torusCenter‖ → f y = 0) : IsScalarTest (torusPeriodize f) :=
  ⟨contDiff_torusPeriodize hf hzero, isTorusPeriodic_torusPeriodize f⟩

end Euler2D

end
