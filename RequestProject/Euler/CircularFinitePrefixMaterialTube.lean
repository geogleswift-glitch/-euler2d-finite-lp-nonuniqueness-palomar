module

public import RequestProject.Euler.CircularFinitePrefixCanonicalUniqueness
public import RequestProject.Euler.CircularFiniteRealRadialFeedback
public import RequestProject.Euler.CircularFourierConstraints

/-! A valid actual prefix path supplies its genuine material geometry.
Only active interfaces are extended into the full index set; no geometric
claim is made about deeper interfaces. Fourfold symmetry follows from
the same original particle map and the original ancient initial sample. -/

@[expose] public section

set_option maxHeartbeats 6500000
set_option maxRecDepth 4000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) prefixTubeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) prefixTubeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) prefixTubeC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) prefixTubeC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

def finiteCircularPrefixExtension {E : Type*} [Zero E] {N k : ℕ}
    (Z : FiniteCircularIndex k → E) (p : FiniteCircularIndex N) : E :=
  if h : p.1.val ≤ k then Z (⟨p.1.val, Nat.lt_succ_of_le h⟩, p.2) else 0

theorem finiteCircularPrefixExtension_at {E : Type*} [Zero E] {N k : ℕ}
    (hk : k ≤ N) (Z : FiniteCircularIndex k → E) (p : FiniteCircularIndex k) :
    finiteCircularPrefixExtension Z (finiteCircularPrefixIndex hk p) = Z p := by
  rcases p with ⟨⟨i, hi⟩, j⟩
  change (if h : i ≤ k then Z (⟨i, Nat.lt_succ_of_le h⟩, j) else 0) =
    Z (⟨i, hi⟩, j)
  rw [dif_pos (Nat.le_of_lt_succ hi)]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteCircularInitial_mem_fourfold {s R ρ : ℝ} (hs : s ≤ 0)
    (N : ℕ) (p : FiniteCircularIndex N) :
    finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p ∈
      fourfoldLittleContourSubmodule γ := by
  unfold finiteCircularInitialContours
  apply Submodule.smul_mem
  split_ifs
  · exact P.ancient_fourfold s hs p.2
  · exact littleReferenceCircle_mem_fourfold hγ hγ1.le (circularContourRadii p.2)

theorem exists_uniform_actualPrefix_materialTube :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob a c D : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      0 ≤ D → ∀ {N k : ℕ} (hk : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      let qinner := P.finiteInnerInitialLabel s A₀ b R ρ N k
      let F := S.actualPartialPhaseField qinner hγ hγ1
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceStrength A₀ b)
      let U := S.actualPartialPhaseDomain qinner
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob
      let Zinit : FiniteCircularIndex k → LittleContourSpace γ := fun p =>
        finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hk p)
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      IsBanachTimeDomainTrajectoryOn F U Zinit D X →
      ∀ t ∈ Icc (0 : ℝ) D, ∀ {core δ : ℝ}, δ ≤ cellA / 4 →
      (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      ∀ β : FiniteCircularIndex k → ℝ,
      (∀ p, ‖contourParameterShiftC1 (β p) (X t p).val -
        finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ δ * radScale R ρ p.1) →
      ∃ G : P.FiniteOuterMaterialTube s R ρ N k S t core δ,
        ∀ p : FiniteCircularIndex k,
          G.contours (finiteCircularPrefixIndex hk p) = (X t p).val := by
  obtain ⟨C, hC, hidentify⟩ := P.exists_uniform_finiteEuler_partial_material_identification
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob a c D _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE
    hglobT hc hcR hD N k hk S hS
  dsimp only
  intro X hX t ht core δ hδ hcore β hsmall
  let Z : ℝ → FiniteCircularIndex k → ContourC1Space γ := fun u p => (X u p).val
  have hZ0 : Z 0 = fun p =>
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hk p)).val :=
    congrArg (fun Y : FiniteCircularIndex k → LittleContourSpace γ => fun p => (Y p).val) hX.initial
  have hphase : ∀ u ∈ Icc (0 : ℝ) D, ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
      ‖contourParameterShiftC1 (β p) (Z u p) - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ <
        finiteCircularInterfaceRadius R ρ p / 4 :=
    fun u hu => (hX.mem u hu).2.2.2.1
  have hZc (p : FiniteCircularIndex k) : ContinuousOn (fun u => Z u p) (Icc (0 : ℝ) D) :=
    (LittleContourSpace.inclusion γ).continuous.comp_continuousOn
      ((continuous_apply p).comp_continuousOn hX.continuous)
  have hmat : ∀ u ∈ Icc (0 : ℝ) D, ∀ p θ,
      HasDerivAt (fun v => ContourC1Space.lift γ (Z v p) θ)
        (contourC1BoundaryField (finiteCircularInterfaceStrength A₀ b) (Z u) p θ +
          S.physicalLabelComplexField (P.finiteInnerInitialLabel s A₀ b R ρ N k) u
            (ContourC1Space.lift γ (Z u p) θ)) u := by
    intro u hu
    exact (S.actualPartialPhaseField_material_iff hγ hγ1
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceStrength A₀ b) (hX.hasDerivAt u hu) (hX.mem u hu).2.1).mpr
        (hX.mem u hu).2.2.2.2
  have hDglob : D ≤ Hglob := (hX.mem D ⟨hD, le_rfl⟩).1.2
  have hcoef : 0 ≤ C * A₀ / (1 - ρ / b) :=
    div_nonneg (mul_nonneg hC.le hA) (sub_pos.mpr ((div_lt_one hb).mpr hρb)).le
  have hcD : (5 / 4 : ℝ) + (C * A₀ / (1 - ρ / b)) * D < c :=
    lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_of_nonneg_left hDglob hcoef)) hc
  have hi := hidentify hs hA hb hR hRmax hρ hρ1 hρb hq hqE hD
    (hDglob.trans hglobT) hcD hcR hk S Z hZ0 hphase hZc hmat
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans (hDglob.trans hglobT)⟩
  have hfour (p : FiniteCircularIndex k) (θ : ℝ) :
      ContourC1Space.lift γ (Z t p) (θ + Real.pi / 2) = I * ContourC1Space.lift γ (Z t p) θ := by
    have hinit : ContourC1Space.lift γ (Z 0 p) (θ + Real.pi / 2) =
        I * ContourC1Space.lift γ (Z 0 p) θ := by
      rw [hZ0]
      exact (mem_fourfoldLittleContourSubmodule _).mp
        (P.finiteCircularInitial_mem_fourfold hs N (finiteCircularPrefixIndex hk p)) θ
    apply centeredComplexHomeomorph.injective
    change complexTorusPoint _ = complexTorusPoint _
    rw [← (hi t ht).1 p (θ + Real.pi / 2), hinit,
      ← torusQuarterTurn_complexTorusPoint, hS.forward t htT,
      (hi t ht).1 p θ, torusQuarterTurn_complexTorusPoint]
  have hbox (u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) (p : FiniteCircularIndex k) :
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z u p)) ⊆ torusBox := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨βu, hβu⟩ := hphase u hu
    have hn := norm_lt_of_mem_contourRadialFill_of_shift (Z u p)
      (finiteCircularReferenceC1 hγ hγ1 R ρ p) (finiteCircularInterfaceRadius_pos hR hρ p)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ p) (βu p) (hβu p).le hz
    have hr := finiteCircularInterfaceRadius_le hR hρ hρ1 p
    apply norm_sub_center_lt_one_mem_box
    rw [complexTorusPoint_sub_center_norm]
    linarith
  let W : FiniteCircularIndex N → ContourC1Space γ := finiteCircularPrefixExtension (Z t)
  let βfull : FiniteCircularIndex N → ℝ := finiteCircularPrefixExtension β
  have hWa (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k) (i : Fin 2) :
      W (j, i) = Z t (⟨j.val, Nat.lt_succ_of_le hj⟩, i) := by
    simp only [W, finiteCircularPrefixExtension, dif_pos hj]
  have hβa (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k) (i : Fin 2) :
      βfull (j, i) = β (⟨j.val, Nat.lt_succ_of_le hj⟩, i) := by
    simp only [βfull, finiteCircularPrefixExtension, dif_pos hj]
  have hquarter (p : FiniteCircularIndex k) :
      ‖contourParameterShiftC1 (β p) (Z t p) - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
        finiteCircularInterfaceRadius R ρ p / 4 := by
    have hd := (circularContourRadii_bounds p.2).2.1
    have hm := mul_le_mul_of_nonneg_right (hδ.trans (by linarith : cellA / 4 ≤ circularContourRadii p.2 / 4))
      (radScale_pos hR hρ p.1).le
    exact (hsmall p).trans (by dsimp only [finiteCircularInterfaceRadius]; nlinarith only [hm])
  refine ⟨{
    contours := W
    reference := finiteCircularReferenceC1 hγ hγ1 R ρ
    shifts := βfull
    reference_lift := ?_
    quarter_tube := ?_
    relative_tube := ?_
    core := hcore
    fourfold := ?_
    initial_box := ?_
    current_box := ?_
    images := ?_
  }, ?_⟩
  · intro j hj i
    simpa only [finiteCircularInterfaceRadius, mul_comm] using
      lift_finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)
  · intro j hj i
    rw [hWa j hj i, hβa j hj i]
    simpa only [finiteCircularInterfaceRadius, finiteCircularReferenceC1, mul_comm] using
      hquarter (⟨j.val, Nat.lt_succ_of_le hj⟩, i)
  · intro j hj i
    rw [hWa j hj i, hβa j hj i]
    simpa only [Z, finiteCircularReferenceC1, mul_comm] using
      hsmall (⟨j.val, Nat.lt_succ_of_le hj⟩, i)
  · intro j hj i θ
    rw [hWa j hj i]
    exact hfour (⟨j.val, Nat.lt_succ_of_le hj⟩, i) θ
  · intro j hj i
    have hh := hbox 0 ⟨le_rfl, hD⟩ (⟨j.val, Nat.lt_succ_of_le hj⟩, i)
    simpa only [hZ0, finiteCircularPrefixIndex] using hh
  · intro j hj i
    rw [hWa j hj i]
    exact hbox t ht (⟨j.val, Nat.lt_succ_of_le hj⟩, i)
  · intro j hj i
    rw [hWa j hj i]
    simpa only [hZ0, finiteCircularPrefixIndex] using
      (hi t ht).2.1 (⟨j.val, Nat.lt_succ_of_le hj⟩, i)
  · intro p
    exact finiteCircularPrefixExtension_at hk (Z t) p

end CircularMaterialTransferProfile
end Euler2D

end
