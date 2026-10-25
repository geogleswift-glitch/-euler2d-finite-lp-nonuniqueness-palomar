module

public import RequestProject.Euler.CircularFiniteSourceSupport
public import RequestProject.Euler.CircularFourierOperatorBounds

/-! The actual finite initial contours are circular outer interfaces and
one copy of the same ancient inner cell. A single sufficiently negative
ancient sample makes every finite family admissible, at all cutoffs. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) finiteInitialLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) finiteInitialLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) finiteInitialC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) finiteInitialC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

abbrev FiniteCircularIndex (N : ℕ) := Fin (N + 1) × Fin 2

def finiteCircularInterfaceRadius (R ρ : ℝ) {N : ℕ} (p : FiniteCircularIndex N) : ℝ :=
  radScale R ρ p.1 * circularContourRadii p.2

def finiteCircularReferenceC1 {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (R ρ : ℝ) {N : ℕ} (p : FiniteCircularIndex N) : ContourC1Space γ :=
  radScale R ρ p.1 • circularReferenceC1 hγ hγ1 p.2

def finiteCircularInitialContours {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (R ρ : ℝ) (Z : Fin 2 → LittleContourSpace γ) (N : ℕ)
    (p : FiniteCircularIndex N) : LittleContourSpace γ :=
  radScale R ρ p.1 • if (p.1 : ℕ) = N then Z p.2 else littleCircularReference hγ hγ1 p.2

theorem norm_finiteCircularInitialContours_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (Z : Fin 2 → LittleContourSpace γ) (N : ℕ) :
    ‖finiteCircularInitialContours hγ hγ1 R ρ Z N‖ ≤
      R * max ‖Z‖ ‖littleCircularReference hγ hγ1‖ := by
  let B := max ‖Z‖ ‖littleCircularReference hγ hγ1‖
  have hB : 0 ≤ B := (norm_nonneg Z).trans (le_max_left _ _)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hR.le hB)).mpr
  intro p
  have hr : 0 < radScale R ρ p.1 := mul_pos hR (pow_pos hρ p.1)
  have hrR : radScale R ρ p.1 ≤ R :=
    mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hterm : ‖if (p.1 : ℕ) = N then Z p.2 else littleCircularReference hγ hγ1 p.2‖ ≤ B := by
    split_ifs
    · exact (norm_le_pi_norm Z p.2).trans (le_max_left _ _)
    · exact (norm_le_pi_norm (littleCircularReference hγ hγ1) p.2).trans (le_max_right _ _)
  change ‖radScale R ρ p.1 • _‖ ≤ R * B
  rw [norm_smul, Real.norm_of_nonneg hr.le]
  exact (mul_le_mul_of_nonneg_left hterm hr.le).trans (mul_le_mul_of_nonneg_right hrR hB)

theorem radScale_le_ratio_of_lt {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {j k : ℕ} (hjk : j < k) : radScale R ρ k ≤ ρ * radScale R ρ j := by
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hjk)
  calc
    _ = (ρ * radScale R ρ j) * ρ ^ l := by rw [hl]; simp only [radScale, pow_add, pow_succ]; ring
    _ ≤ _ := mul_le_of_le_one_right (mul_nonneg hρ.le (mul_pos hR (pow_pos hρ j)).le)
      (pow_le_one₀ hρ.le hρ1)

theorem norm_finiteCircularReference_value {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) {N : ℕ} (p : FiniteCircularIndex N)
    (x : ContourCircle) :
    ‖ContourC1Space.toBCF γ (finiteCircularReferenceC1 hγ hγ1 R ρ p) x‖ =
      finiteCircularInterfaceRadius R ρ p := by
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change ‖radScale R ρ p.1 • refCircle (circularContourRadii p.2) θ‖ = _
  have hr : 0 ≤ radScale R ρ p.1 := (mul_pos hR (pow_pos hρ p.1)).le
  rw [norm_smul, Real.norm_of_nonneg hr,
    norm_refCircle_actual, abs_of_pos (circularContourRadii_bounds p.2).1]
  rfl

theorem finiteCircular_initial_close {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {R ρ η : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hη : 0 ≤ η)
    (Z : Fin 2 → LittleContourSpace γ)
    (hZ : ∀ i, ‖(Z i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) (N : ℕ)
    (p : FiniteCircularIndex N) :
    ‖(finiteCircularInitialContours hγ hγ1 R ρ Z N p).val -
      finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ η * radScale R ρ p.1 := by
  have hr : 0 ≤ radScale R ρ p.1 := (mul_pos hR (pow_pos hρ p.1)).le
  by_cases hp : (p.1 : ℕ) = N
  · unfold finiteCircularInitialContours finiteCircularReferenceC1
    rw [if_pos hp]
    change ‖radScale R ρ p.1 • (Z p.2).val -
        radScale R ρ p.1 • circularReferenceC1 hγ hγ1 p.2‖ ≤ _
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hr, mul_comm η]
    exact mul_le_mul_of_nonneg_left (hZ p.2) hr
  · simp only [finiteCircularInitialContours, if_neg hp, finiteCircularReferenceC1]
    change ‖radScale R ρ p.1 • circularReferenceC1 hγ hγ1 p.2 -
      radScale R ρ p.1 • circularReferenceC1 hγ hγ1 p.2‖ ≤ _
    simp only [sub_self, norm_zero]
    exact mul_nonneg hη hr

theorem admissible_scaledCircular_family_of_close {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ η : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρa : ρ ≤ cellA / 4)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    {N : ℕ} (Z : FiniteCircularIndex N → LittleContourSpace γ)
    (hZ : ∀ p, ‖(Z p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ η * radScale R ρ p.1) :
    IsAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) Z := by
  have hr (j : ℕ) : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
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
  have hord (p q : FiniteCircularIndex N) (hpq : (p.1 : ℕ) < q.1) :
      ContourCrossSeparated (Z p).val (Z q).val ((cellA / 4) * radScale R ρ p.1) := by
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
    have hlower : (cellA - η) * radScale R ρ p.1 ≤ ‖ContourC1Space.toBCF γ (Z p).val x‖ := by
      exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hpk η) (hr p.1).le).trans hp
    have hηr := mul_le_mul_of_nonneg_right hηa (hr p.1).le
    have hn := norm_sub_norm_le (ContourC1Space.toBCF γ (Z p).val x)
      (ContourC1Space.toBCF γ (Z q).val y)
    have har := mul_nonneg cellA_pos.le (hr p.1).le
    nlinarith only [hlower, hupper, hηr, hn, har]
  constructor
  · intro p
    have hηπ : η * Real.pi < 2 * circularContourRadii p.2 := by
      have hm := mul_le_mul_of_nonneg_right hηa Real.pi_pos.le
      have ha := (circularContourRadii_bounds p.2).2.1
      nlinarith [Real.pi_lt_four, cellA_pos]
    apply (hZ p).trans_lt
    apply (lt_div_iff₀ Real.pi_pos).mpr
    dsimp only [finiteCircularInterfaceRadius]
    nlinarith [mul_pos (sub_pos.mpr hηπ) (hr p.1)]
  · intro p q hpq
    rcases lt_trichotomy (p.1 : ℕ) (q.1 : ℕ) with hlt | heq | hgt
    · exact ⟨(cellA / 4) * radScale R ρ p.1,
        mul_pos (div_pos cellA_pos (by norm_num)) (hr p.1), hord p q hlt⟩
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
      refine ⟨((1 - cellA) * radScale R ρ p.1) / 2,
        div_pos (mul_pos (sub_pos.mpr cellA_lt_one) (hr p.1)) (by norm_num), ?_⟩
      exact contourCrossSeparated_of_norm_sub_le _ _ _ _ hsep hδ
    · refine ⟨(cellA / 4) * radScale R ρ q.1,
        mul_pos (div_pos cellA_pos (by norm_num)) (hr q.1), ?_⟩
      intro x y
      simpa only [norm_sub_rev] using hord q p hgt y x

end Euler2D

end
