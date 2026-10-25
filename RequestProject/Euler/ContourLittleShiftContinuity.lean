module

public import RequestProject.Euler.ContourFourierModeNorm
public import RequestProject.Euler.ContourParameterShift
public import RequestProject.Euler.ContourComplexC1Space

/-! Parameter translation is strongly continuous in the actual little
C¹ Hölder norm. Smooth loops have a genuine Lipschitz translation orbit;
the unchanged smooth-closure definition extends this to every little loop. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ContDiff ENNReal

namespace Euler2D

local instance (priority := 2000) shiftContC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) shiftContC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) shiftContLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) shiftContLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

set_option maxHeartbeats 800000 in
theorem norm_contourParameterShiftC1_sub_le_of_deriv_bounds {γ : ℝ≥0} (hγ1 : γ ≤ 1)
    (Z : ContourC1Space γ) (hs : ContDiff ℝ ∞ (ContourC1Space.lift γ Z))
    (A B C : ℝ≥0)
    (hA : ∀ θ, ‖deriv (ContourC1Space.lift γ Z) θ‖ ≤ A)
    (hB : ∀ θ, ‖deriv (deriv (ContourC1Space.lift γ Z)) θ‖ ≤ B)
    (hC : ∀ θ, ‖deriv (deriv (deriv (ContourC1Space.lift γ Z))) θ‖ ≤ C)
    (b a : ℝ) :
    ‖contourParameterShiftC1 b Z - contourParameterShiftC1 a Z‖ ≤
      ((A : ℝ) + B + C * Real.pi ^ (1 - (γ : ℝ))) * |b - a| := by
  let f := ContourC1Space.lift γ Z
  let W := contourParameterShiftC1 b Z - contourParameterShiftC1 a Z
  have hs1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hs).2
  have hs2 : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hs1).2
  have hw (θ : ℝ) : ContourC1Space.lift γ W θ = f (θ + b) - f (θ + a) := by
    simp only [W, ContourC1Space.lift_sub, Pi.sub_apply, lift_contourParameterShiftC1, f]
  have hd (θ : ℝ) : ContourC1Space.derivative γ W (θ : ContourCircle) =
      deriv f (θ + b) - deriv f (θ + a) := by
    have hb := ((contDiff_infty_iff_deriv.mp hs).1 (θ + b)).hasDerivAt.scomp θ
      ((hasDerivAt_id θ).add_const b)
    have ha := ((contDiff_infty_iff_deriv.mp hs).1 (θ + a)).hasDerivAt.scomp θ
      ((hasDerivAt_id θ).add_const a)
    have h := hb.sub ha
    simp only [one_smul] at h
    change HasDerivAt (fun θ => f (θ + b) - f (θ + a))
      (deriv f (θ + b) - deriv f (θ + a)) θ at h
    have he : ContourC1Space.lift γ W = fun θ => f (θ + b) - f (θ + a) := funext hw
    rw [← he] at h
    exact (ContourC1Space.hasDerivAt_lift W θ).unique h
  have hv (x : ContourCircle) :
      ‖ContourC1Space.toBCF γ W x‖ ≤ (A : ℝ) * |b - a| := by
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ‖ContourC1Space.lift γ W θ‖ ≤ _
    rw [hw]
    simpa only [add_sub_add_left_eq_sub] using
      norm_sub_le_of_contDiff_deriv_bound (hs.of_le (by simp)) A.coe_nonneg hA (θ + b) (θ + a)
  have hdB (x : ContourCircle) :
      ‖ContourC1Space.derivative γ W x‖ ≤ (B : ℝ) * |b - a| := by
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hd]
    simpa only [add_sub_add_left_eq_sub] using
      norm_sub_le_of_contDiff_deriv_bound (hs1.of_le (by simp)) B.coe_nonneg hB (θ + b) (θ + a)
  let D : ℝ≥0 := ⟨(C : ℝ) * |b - a|, by positivity⟩
  have hl : LipschitzWith D (fun x => ContourC1Space.derivative γ W x) := by
    apply lipschitzWith_contour_of_deriv_bound
    · have h : ContDiff ℝ ∞ (fun θ : ℝ => deriv f (θ + b) - deriv f (θ + a)) :=
        (hs1.comp (contDiff_id.add contDiff_const)).sub
        (hs1.comp (contDiff_id.add contDiff_const))
      simpa only [hd] using (h.of_le (by simp) : ContDiff ℝ 1
        (fun θ : ℝ => deriv f (θ + b) - deriv f (θ + a)))
    · intro θ
      have hb := ((contDiff_infty_iff_deriv.mp hs1).1 (θ + b)).hasDerivAt.scomp θ
        ((hasDerivAt_id θ).add_const b)
      have ha := ((contDiff_infty_iff_deriv.mp hs1).1 (θ + a)).hasDerivAt.scomp θ
        ((hasDerivAt_id θ).add_const a)
      have h := hb.sub ha
      simp only [one_smul] at h
      change HasDerivAt (fun θ => deriv f (θ + b) - deriv f (θ + a))
        (deriv (deriv f) (θ + b) - deriv (deriv f) (θ + a)) θ at h
      have he : (fun θ : ℝ => ContourC1Space.derivative γ W (θ : ContourCircle)) =
          fun θ => deriv f (θ + b) - deriv f (θ + a) := funext hd
      rw [he, h.deriv]
      simpa only [D, NNReal.coe_mk, add_sub_add_left_eq_sub] using
        norm_sub_le_of_contDiff_deriv_bound (hs2.of_le (by simp)) C.coe_nonneg hC (θ + b) (θ + a)
  have hdiam (x y : ContourCircle) : edist x y ≤ (Real.toNNReal Real.pi : ℝ≥0∞) := by
    rw [edist_dist]
    change ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal Real.pi
    exact ENNReal.ofReal_le_ofReal (contour_dist_le_pi x y)
  have hh := hl.holderWith.of_le (D := Real.toNNReal Real.pi) hdiam hγ1
  have hn := norm_contourC1_le_of_uniform_holder_bounds W
    ⟨(A : ℝ) * |b - a|, by positivity⟩ ⟨(B : ℝ) * |b - a|, by positivity⟩
    (D * (Real.toNNReal Real.pi) ^ (1 - (γ : ℝ))) hv hdB hh
  convert hn using 1
  simp only [D, NNReal.coe_mk, NNReal.coe_mul, NNReal.coe_rpow,
    Real.coe_toNNReal _ Real.pi_pos.le]
  ring

theorem lipschitz_contourParameterShiftC1_of_smooth {γ : ℝ≥0} (hγ1 : γ ≤ 1)
    (Z : ContourC1Space γ) (hs : Z ∈ smoothContourSubmodule γ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun b : ℝ => contourParameterShiftC1 b Z) := by
  change ContDiff ℝ ∞ (ContourC1Space.lift γ Z) at hs
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have hs2 := (contDiff_infty_iff_deriv.mp hs1).2
  have hs3 := (contDiff_infty_iff_deriv.mp hs2).2
  have hp1 := periodic_deriv_contour (ContourC1Space.periodic_lift Z)
    (contDiff_infty_iff_deriv.mp hs).1
  have hp2 := periodic_deriv_contour hp1 (contDiff_infty_iff_deriv.mp hs1).1
  have hp3 := periodic_deriv_contour hp2 (contDiff_infty_iff_deriv.mp hs2).1
  obtain ⟨A, hA, hbA⟩ :=
    (hp1.isBounded_of_continuous (by positivity) hs1.continuous).exists_pos_norm_le
  obtain ⟨B, hB, hbB⟩ :=
    (hp2.isBounded_of_continuous (by positivity) hs2.continuous).exists_pos_norm_le
  obtain ⟨C, hC, hbC⟩ :=
    (hp3.isBounded_of_continuous (by positivity) hs3.continuous).exists_pos_norm_le
  refine ⟨⟨A + B + C * Real.pi ^ (1 - (γ : ℝ)), by positivity⟩,
    LipschitzWith.of_dist_le_mul (fun b a => ?_)⟩
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using
    norm_contourParameterShiftC1_sub_le_of_deriv_bounds hγ1 Z hs
      ⟨A, hA.le⟩ ⟨B, hB.le⟩ ⟨C, hC.le⟩
      (fun θ => hbA _ (Set.mem_range_self θ))
      (fun θ => hbB _ (Set.mem_range_self θ))
      (fun θ => hbC _ (Set.mem_range_self θ)) b a

set_option maxHeartbeats 800000 in
theorem continuous_contourParameterShiftLittleCLM {γ : ℝ≥0} (hγ1 : γ ≤ 1)
    (Z : LittleContourSpace γ) :
    Continuous (fun b : ℝ => contourParameterShiftLittleCLM γ b Z) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨W, hs, hW⟩ := LittleContourSpace.exists_smooth_approximation Z
    (div_pos hε (by norm_num : (0 : ℝ) < 4))
  obtain ⟨K, hK⟩ := lipschitz_contourParameterShiftC1_of_smooth hγ1 W hs
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hK.continuous.continuousAt
    (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun b hb => ?_⟩
  have hmid := hclose hb
  rw [dist_eq_norm] at hmid
  change dist (contourParameterShiftC1 b Z.val) (contourParameterShiftC1 a Z.val) < ε
  rw [dist_eq_norm]
  have herr (c : ℝ) :
      ‖contourParameterShiftC1 c Z.val - contourParameterShiftC1 c W‖ = ‖Z.val - W‖ := by
    change ‖contourParameterShiftC1CLM γ c Z.val - contourParameterShiftC1CLM γ c W‖ = _
    rw [← map_sub]
    exact norm_contourParameterShiftC1 c (Z.val - W)
  have htri :
      ‖contourParameterShiftC1 b Z.val - contourParameterShiftC1 a Z.val‖ ≤
        ‖contourParameterShiftC1 b Z.val - contourParameterShiftC1 b W‖ +
        ‖contourParameterShiftC1 b W - contourParameterShiftC1 a W‖ +
        ‖contourParameterShiftC1 a W - contourParameterShiftC1 a Z.val‖ := by
    calc
      _ = ‖(contourParameterShiftC1 b Z.val - contourParameterShiftC1 b W) +
          (contourParameterShiftC1 b W - contourParameterShiftC1 a W) +
          (contourParameterShiftC1 a W - contourParameterShiftC1 a Z.val)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
  rw [herr b, norm_sub_rev (contourParameterShiftC1 a W), herr a] at htri
  linarith

theorem continuous_contourParameterShiftFamilyCLM {ι : Type*} [Fintype ι]
    {γ : ℝ≥0} (hγ1 : γ ≤ 1) (Z : ι → LittleContourSpace γ) :
    Continuous (fun b : ι → ℝ => contourParameterShiftFamilyCLM γ b Z) := by
  apply continuous_pi
  intro i
  exact (continuous_contourParameterShiftLittleCLM hγ1 (Z i)).comp (continuous_apply i)

attribute [local instance] HolderFunctionSpace.complexScalarNormedSpace
  ContourC1Space.complexScalarNormedSpace

theorem continuous_contourRotationLittleCLM {γ : ℝ≥0} (hγ1 : γ ≤ 1)
    (Z : LittleContourSpace γ) :
    Continuous (fun b : ℝ => contourRotationLittleCLM γ b Z) := by
  have hc : Continuous (fun b : ℝ => contourParameterShiftC1 (-b) Z.val) :=
    (LittleContourSpace.inclusion γ).continuous.comp
      ((continuous_contourParameterShiftLittleCLM hγ1 Z).comp continuous_neg)
  have he : Continuous (fun b : ℝ => Complex.exp ((b : ℂ) * I)) :=
    (Complex.continuous_ofReal.mul continuous_const).cexp
  have h := he.smul hc
  have hrot (b : ℝ) :
      Complex.exp ((b : ℂ) * I) • contourParameterShiftC1 (-b) Z.val =
        (contourRotationLittleCLM γ b Z).val := by
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ContourC1Space.lift γ (ContourC1Space.complexScale _ _) θ =
      LittleContourSpace.lift γ (contourRotationLittleCLM γ b Z) θ
    simp only [ContourC1Space.lift_complexScale, lift_contourParameterShiftC1,
      lift_contourRotationLittleCLM, rotShift, sub_eq_add_neg]
    rfl
  simp_rw [hrot] at h
  exact h.subtype_mk _

end Euler2D

end
