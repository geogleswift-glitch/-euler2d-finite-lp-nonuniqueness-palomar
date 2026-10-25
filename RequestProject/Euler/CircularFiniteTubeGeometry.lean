module

public import RequestProject.Euler.CircularAncientFiniteInitialFamily

/-! A strict circular tube has positive uniform chord and interface
separation constants at each fixed finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) circularTubeGeometryLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularTubeGeometryC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

def finiteCircularTubeChordConstant (R ρ : ℝ) (N : ℕ) : ℝ :=
  cellA * radScale R ρ N / Real.pi

def finiteCircularTubeSeparationConstant (R ρ : ℝ) (N : ℕ) : ℝ :=
  (min cellA (1 - cellA) / 4) * radScale R ρ N

theorem finiteCircularTubeChordConstant_pos {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) : 0 < finiteCircularTubeChordConstant R ρ N :=
  div_pos (mul_pos cellA_pos (mul_pos hR (pow_pos hρ N))) Real.pi_pos

theorem finiteCircularTubeSeparationConstant_pos {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) : 0 < finiteCircularTubeSeparationConstant R ρ N :=
  mul_pos (div_pos (lt_min cellA_pos (sub_pos.mpr cellA_lt_one)) (by norm_num))
    (mul_pos hR (pow_pos hρ N))

theorem finiteCircular_close_uniform_geometry {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ η : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρa : ρ ≤ cellA / 4)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    {N : ℕ} (Z : FiniteCircularIndex N → LittleContourSpace γ)
    (hZ : ∀ p, ‖(Z p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ η * radScale R ρ p.1) :
    (∀ p, ContourC1Space.HasChordArcLower (Z p).val (finiteCircularTubeChordConstant R ρ N)) ∧
    (∀ p q, p ≠ q → ContourCrossSeparated (Z p).val (Z q).val
      (finiteCircularTubeSeparationConstant R ρ N)) := by
  have hρ1 : ρ ≤ 1 := by linarith [cellA_lt_one]
  have hr (j : ℕ) : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  have hmin (p : FiniteCircularIndex N) : radScale R ρ N ≤ radScale R ρ p.1 :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hρ.le hρ1 (Nat.le_of_lt_succ p.1.isLt)) hR.le
  have hη1 : η ≤ 1 := by linarith [cellA_lt_one]
  have hval (p : FiniteCircularIndex N) (x : ContourCircle) :
      (circularContourRadii p.2 - η) * radScale R ρ p.1 ≤ ‖ContourC1Space.toBCF γ (Z p).val x‖ ∧
      ‖ContourC1Space.toBCF γ (Z p).val x‖ ≤ (circularContourRadii p.2 + η) * radScale R ρ p.1 := by
    have hd := (ContourC1Space.norm_eval_le
      ((Z p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p) x).trans (hZ p)
    have hn := norm_finiteCircularReference_value hγ hγ1 hR hρ p x
    have h₁ := norm_sub_norm_le (ContourC1Space.toBCF γ (Z p).val x)
      (ContourC1Space.toBCF γ (finiteCircularReferenceC1 hγ hγ1 R ρ p) x)
    have h₂ := norm_sub_norm_le (ContourC1Space.toBCF γ (finiteCircularReferenceC1 hγ hγ1 R ρ p) x)
      (ContourC1Space.toBCF γ (Z p).val x)
    rw [hn] at h₁ h₂
    change ‖ContourC1Space.toBCF γ (Z p).val x -
      ContourC1Space.toBCF γ (finiteCircularReferenceC1 hγ hγ1 R ρ p) x‖ ≤ _ at hd
    rw [norm_sub_rev] at h₂
    dsimp only [finiteCircularInterfaceRadius] at h₁ h₂
    constructor <;> nlinarith
  have hσA (p : FiniteCircularIndex N) : finiteCircularTubeSeparationConstant R ρ N ≤
      (cellA / 4) * radScale R ρ p.1 := by
    dsimp only [finiteCircularTubeSeparationConstant]
    exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
      (hr N).le).trans (mul_le_mul_of_nonneg_left (hmin p)
        (div_nonneg cellA_pos.le (by norm_num)))
  have hσgap (p : FiniteCircularIndex N) : finiteCircularTubeSeparationConstant R ρ N ≤
      ((1 - cellA) * radScale R ρ p.1) / 2 := by
    have hh : finiteCircularTubeSeparationConstant R ρ N ≤
        ((1 - cellA) / 4) * radScale R ρ p.1 := by
      dsimp only [finiteCircularTubeSeparationConstant]
      exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
        (hr N).le).trans (mul_le_mul_of_nonneg_left (hmin p) (by linarith [cellA_lt_one]))
    have hg : 0 ≤ (1 - cellA) * radScale R ρ p.1 := mul_nonneg (by linarith [cellA_lt_one]) (hr _).le
    nlinarith
  have hord (p q : FiniteCircularIndex N) (hpq : (p.1 : ℕ) < q.1) :
      ContourCrossSeparated (Z p).val (Z q).val (finiteCircularTubeSeparationConstant R ρ N) := by
    intro x y
    have hp := (hval p x).1
    have hq := (hval q y).2
    have hpk := (circularContourRadii_bounds p.2).2.1
    have hqk := (circularContourRadii_bounds q.2).2.2
    have hrr := radScale_le_ratio_of_lt hR hρ hρ1 hpq
    have hrad : radScale R ρ q.1 ≤ (cellA / 4) * radScale R ρ p.1 :=
      hrr.trans (mul_le_mul_of_nonneg_right hρa (hr p.1).le)
    have hupper : ‖ContourC1Space.toBCF γ (Z q).val y‖ ≤ (cellA / 2) * radScale R ρ p.1 := by
      have hn : (circularContourRadii q.2 + η) * radScale R ρ q.1 ≤ 2 * radScale R ρ q.1 := by
        nlinarith [hr q.1]
      exact (hq.trans hn).trans (by nlinarith)
    have hlower : (cellA - η) * radScale R ρ p.1 ≤ ‖ContourC1Space.toBCF γ (Z p).val x‖ :=
      (mul_le_mul_of_nonneg_right (sub_le_sub_right hpk η) (hr p.1).le).trans hp
    have hηr := mul_le_mul_of_nonneg_right hηa (hr p.1).le
    have hn := norm_sub_norm_le (ContourC1Space.toBCF γ (Z p).val x)
      (ContourC1Space.toBCF γ (Z q).val y)
    have har := mul_nonneg cellA_pos.le (hr p.1).le
    exact (hσA p).trans (by nlinarith only [hlower, hupper, hηr, hn, har])
  constructor
  · intro p
    have hbase : ContourC1Space.HasChordArcLower
        (finiteCircularReferenceC1 hγ hγ1 R ρ p) (2 * finiteCircularInterfaceRadius R ρ p / Real.pi) := by
      intro θ τ hτ
      rw [lift_finiteCircularReferenceC1 hγ hγ1 R ρ p]
      exact refCircle_short_chord (finiteCircularInterfaceRadius_pos hR hρ p).le θ hτ
    apply ContourC1Space.hasChordArcLower_mono _
      (ContourC1Space.hasChordArcLower_of_norm_sub _ _ hbase)
    have hd := mul_le_mul_of_nonneg_right (hZ p) Real.pi_pos.le
    have hηπ : η * Real.pi ≤ cellA := by
      have hh := mul_le_mul_of_nonneg_left Real.pi_lt_four.le hη
      nlinarith [cellA_pos]
    have hsmall := mul_le_mul_of_nonneg_right hηπ (hr p.1).le
    have hrad := mul_le_mul_of_nonneg_right (circularContourRadii_bounds p.2).2.1 (hr p.1).le
    have hminA := mul_le_mul_of_nonneg_left (hmin p) cellA_pos.le
    dsimp only [finiteCircularTubeChordConstant, finiteCircularInterfaceRadius]
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith [div_mul_cancel₀ (cellA * radScale R ρ N) Real.pi_ne_zero]
  · intro p q hpq
    rcases lt_trichotomy (p.1 : ℕ) (q.1 : ℕ) with hlt | heq | hgt
    · exact hord p q hlt
    · have hj : p.1 = q.1 := Fin.ext heq
      have hi : p.2 ≠ q.2 := fun h => hpq (Prod.ext hj h)
      have hsep : ContourCrossSeparated
          (finiteCircularReferenceC1 hγ hγ1 R ρ p) (finiteCircularReferenceC1 hγ hγ1 R ρ q)
          ((1 - cellA) * radScale R ρ p.1) := by
        intro x y
        have hn := abs_norm_sub_norm_le
          (ContourC1Space.toBCF γ (finiteCircularReferenceC1 hγ hγ1 R ρ p) x)
          (ContourC1Space.toBCF γ (finiteCircularReferenceC1 hγ hγ1 R ρ q) y)
        rw [norm_finiteCircularReference_value hγ hγ1 hR hρ,
          norm_finiteCircularReference_value hγ hγ1 hR hρ] at hn
        have he : |finiteCircularInterfaceRadius R ρ p - finiteCircularInterfaceRadius R ρ q| =
            (1 - cellA) * radScale R ρ p.1 := by
          dsimp only [finiteCircularInterfaceRadius]
          rw [← hj, ← mul_sub, abs_mul, abs_of_pos (hr p.1)]
          have hi' : |circularContourRadii p.2 - circularContourRadii q.2| = 1 - cellA := by
            generalize hp : p.2 = i at hi ⊢
            generalize hq : q.2 = j at hi ⊢
            fin_cases i <;> fin_cases j <;>
              simp_all [circularContourRadii, abs_of_neg (sub_neg.mpr cellA_lt_one),
                abs_of_pos (sub_pos.mpr cellA_lt_one)]
          rw [hi']
          ring
        simpa only [he] using hn
      have hδ : ‖finiteCircularReferenceC1 hγ hγ1 R ρ p - (Z p).val‖ +
          ‖finiteCircularReferenceC1 hγ hγ1 R ρ q - (Z q).val‖ ≤
          ((1 - cellA) * radScale R ρ p.1) / 2 := by
        have hp := hZ p
        have hq := hZ q
        rw [norm_sub_rev] at hp hq
        rw [← hj] at hq
        have hm := mul_le_mul_of_nonneg_right hηgap (hr p.1).le
        have hgapr := mul_nonneg (sub_pos.mpr cellA_lt_one).le (hr p.1).le
        nlinarith only [hp, hq, hm, hgapr]
      have hh := contourCrossSeparated_of_norm_sub_le _ _ _ _ hsep hδ
      exact fun x y => (hσgap p).trans (hh x y)
    · intro x y
      simpa only [norm_sub_rev] using hord q p hgt y x

end Euler2D

end
