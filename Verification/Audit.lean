module

public import Solution

/-! Independent exact-statement application and axiom checks.
This verification module imports the proved Solution, never Challenge.
Run it separately after the ordinary project build. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

/-- Expand both finite sums independently: the nonlinear term occurs once,
with the usual Euler coefficient and the derivative on its second index. -/
example (v : Euler2D.R2 → Euler2D.R2)
    (test : ℝ → Euler2D.R2 → Euler2D.R2) (t : ℝ) (x : Euler2D.R2) :
    Euler2D.eulerIntegrand v test t x =
      (v x 0 * deriv (fun s => test s x 0) t +
       v x 1 * deriv (fun s => test s x 1) t) +
      ((v x 0 * v x 0 * Euler2D.pd 0 (test t) x 0 +
        v x 0 * v x 1 * Euler2D.pd 1 (test t) x 0) +
       (v x 1 * v x 0 * Euler2D.pd 0 (test t) x 1 +
        v x 1 * v x 1 * Euler2D.pd 1 (test t) x 1)) := by
  simp only [Euler2D.eulerIntegrand, Fin.sum_univ_two]

example (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 ≤ p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∃ datum : Euler2D.L2T,
      (∫ x in Euler2D.torusBox, datum x = 0) ∧
      Euler2D.DivFree datum ∧ Euler2D.MemW1p (ENNReal.ofReal p) datum ∧
      ∃ first second : ℝ → Euler2D.L2T,
      ∃ firstCurl secondCurl : ℝ → Lp ℝ (ENNReal.ofReal p) Euler2D.μT,
        Euler2D.IsWeakEulerSolution T datum first ∧
        Euler2D.IsWeakEulerSolution T datum second ∧
        Euler2D.CurlBounded T (ENNReal.ofReal p) first ∧
        Euler2D.CurlBounded T (ENNReal.ofReal p) second ∧
        StronglyMeasurable firstCurl ∧ StronglyMeasurable secondCurl ∧
        MemLp firstCurl ∞ (volume.restrict (Icc 0 T)) ∧
        MemLp secondCurl ∞ (volume.restrict (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, Euler2D.IsCurl (first t) (firstCurl t)) ∧
        (∀ t ∈ Icc 0 T, Euler2D.IsCurl (second t) (secondCurl t)) ∧
        0 < Euler2D.spaceTimeDistSq T first second := by
  exact PalomarEuler.main_result T hT p hp

set_option pp.all true in
#check @PalomarEuler.main_result

/-- info: 'PalomarEuler.main_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalomarEuler.main_result

/-- info: 'Euler2D.finiteLp_nonuniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Euler2D.finiteLp_nonuniqueness

/-- info: 'Euler2D.limit_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Euler2D.limit_solution

/-- info: 'Euler2D.main_nonuniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Euler2D.main_nonuniqueness

/-- info: 'Euler2D.refinement_uncountable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Euler2D.refinement_uncountable

/-- info: 'Euler2D.exists_bochner_vorticity_of_weakEuler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Euler2D.exists_bochner_vorticity_of_weakEuler

/-- info: 'Euler2D.exists_bochner_vorticity_of_weakEuler_lowerExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Euler2D.exists_bochner_vorticity_of_weakEuler_lowerExponent
