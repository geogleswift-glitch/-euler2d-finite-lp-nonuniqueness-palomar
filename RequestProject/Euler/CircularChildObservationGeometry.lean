module

public import RequestProject.Euler.CircularFiniteWeightedMaterialTube
public import RequestProject.Euler.CircularCanonicalCrossPrefixReset
public import RequestProject.Euler.CircularFiniteAncestorPointwiseVelocity

/-! The true parent prefix supplies exactly the child observation
geometry. Its extra factor h is converted into the child's weights;
every smaller material tube is a restriction of one actual tube. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem norm_ancestor_of_small_parent_controls {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h Cw Ccur : ℝ} (hh : 0 < h) {k : ℕ} (hk : 0 < k) (x : ℕ → E)
    (hZ : weightedFamilyNorm h (k - 1) x ≤ Cw * h) (hcur : ‖x (k - 1)‖ ≤ Ccur * h)
    (j : Fin k) : ‖x j‖ ≤ h ^ (k - (j : ℕ)) * max Cw Ccur := by
  by_cases hj : (j : ℕ) < k - 1
  · have hpower : (k - 1 - (j : ℕ)) + 1 = k - (j : ℕ) := by omega
    calc
      _ ≤ h ^ (k - 1 - (j : ℕ)) * weightedFamilyNorm h (k - 1) x :=
        norm_le_weightedFamilyNorm hh (k - 1) x ⟨j, hj⟩
      _ ≤ h ^ (k - 1 - (j : ℕ)) * (Cw * h) := mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = h ^ (k - (j : ℕ)) * Cw := by rw [← hpower, pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  · have hjeq : (j : ℕ) = k - 1 := by omega
    have hpower : k - (j : ℕ) = 1 := by omega
    calc
      _ = ‖x (k - 1)‖ := by rw [hjeq]
      _ ≤ Ccur * h := hcur
      _ ≤ max Cw Ccur * h := mul_le_mul_of_nonneg_right (le_max_right _ _) hh.le
      _ = _ := by rw [hpower, pow_one]; ring

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def FiniteOuterMaterialTube.restrictPrefix {s R ρ : ℝ} {N k : ℕ}
    {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T} {t c δ : ℝ}
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ) {l : ℕ} (hlk : l ≤ k) :
    P.FiniteOuterMaterialTube s R ρ N l S t c δ where
  contours := G.contours
  reference := G.reference
  shifts := G.shifts
  reference_lift := fun j hj i => G.reference_lift j (hj.trans hlk) i
  quarter_tube := fun j hj i => G.quarter_tube j (hj.trans hlk) i
  relative_tube := fun j hj i => G.relative_tube j (hj.trans hlk) i
  core := G.core
  fourfold := fun j hj i θ => G.fourfold j (hj.trans hlk) i θ
  initial_box := fun j hj i => G.initial_box j (hj.trans hlk) i
  current_box := fun j hj i => G.current_box j (hj.trans hlk) i
  images := fun j hj i => G.images j (hj.trans hlk) i

theorem exists_uniform_actualParent_child_observation_geometry :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob a d Dphys : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 4 →
      0 ≤ Dphys → ∀ (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ ((Nat.sub_le k 1).trans hkN) S Dphys Y →
      ∀ t ∈ Icc (0 : ℝ) Dphys, ∀ entrance τ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b (k - 1)) entrance τ = t →
      ∀ {core δ C₀ Cw Ccur : ℝ},
      δ ≤ cellA / 4 → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      0 < C₀ → C₀ * ρ ^ 6 ≤ 1 → 0 ≤ Cw →
      (C₀ * ρ ^ 6) * (Cw * (C₀ * ρ ^ 6)) ≤ δ → Ccur * (C₀ * ρ ^ 6) ≤ δ →
      let h := C₀ * ρ ^ 6
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) entrance Y τ
      weightedFamilyNorm h (k - 1) x ≤ Cw * h → ‖x (k - 1)‖ ≤ Ccur * h →
      ∃ G : ∀ j : Fin k, P.FiniteOuterMaterialTube s R ρ N (finiteAncestorPointwiseIndex hkN j) S t core δ,
        ∀ (j : Fin k) i,
          let l := finiteAncestorPointwiseIndex hkN j
          ‖contourParameterShiftC1 ((G j).shifts (l, i)) ((G j).contours (l, i)) - (G j).reference (l, i)‖ ≤
            radScale R ρ j * (h ^ (k - (j : ℕ)) * max Cw Ccur) := by
  obtain ⟨C, hC, hgeo⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob a d Dphys _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE
    hglobT hdrift hdR hDphys N k hk hkN S hS Y hY t ht entrance τ htime
    core δ C₀ Cw Ccur hδ hcore hC₀ hh1 hCw hsmall hcurSmall h x hZ hcur
  let W := canonicalPrefixAbsoluteFamily A₀ b R ρ (k - 1) entrance Y τ
  let u : ℕ → ℝ := fun j => ampScale A₀ b j * entrance + b ^ (k - 1 - j) * τ
  let φ : ℕ → ℝ := fun j => t * finiteAncestorAngularVelocity A₀ b j
  have hh : 0 < h := mul_pos hC₀ (pow_pos hρ 6)
  have hcur' : ‖W (k - 1) - littleCircularMaterialContours hγ hγ1 (u (k - 1))‖ ≤ δ :=
    hcur.trans hcurSmall
  obtain ⟨Gparent, _hGparent, hownq⟩ := hgeo (core := core) (δ := δ) (C₀ := C₀) (K := Cw * h)
    hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hdR hDphys
    ((Nat.sub_le k 1).trans hkN) S hS Y hY t ht hδ hcore hC₀ hh1
    (mul_nonneg hCw hh.le) hsmall W u φ hZ hcur' (by
      intro p
      have he := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
        (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ (k - 1) entrance τ Y p.1)
      rw [htime] at he
      simpa only [W, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
        Pi.smul_apply] using he.symm)
  let G := fun j : Fin k => FiniteOuterMaterialTube.restrictPrefix P Gparent (show (j : ℕ) ≤ k - 1 by omega)
  refine ⟨G, ?_⟩
  intro j i
  let jp : Fin (k - 1 + 1) := ⟨j, by omega⟩
  have hn := norm_ancestor_of_small_parent_controls hh hk x hZ hcur j
  have hrow := hownq jp i
  exact hrow.trans (mul_le_mul_of_nonneg_left hn (radScale_pos hR hρ j).le)

end CircularMaterialTransferProfile
end Euler2D

end
