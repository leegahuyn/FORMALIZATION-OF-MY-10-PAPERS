import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.LinearAlgebra.Dimension.Free

/-! Exact degree multiplicativity of native one-variable rational substitution. -/

namespace ManuscriptAudit.RationalSubstitutionDegree

open IntermediateField Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Substitute the nonconstant rational function g for X. -/
def substitute (g : RatFunc K) (hg : ¬ ∃ c : K, g = RatFunc.C c) :
    RatFunc K →ₐ[K] RatFunc K :=
  (adjoin K ({g} : Set (RatFunc K))).val.comp
    (RatFunc.algEquivOfTranscendental g (g.transcendental_of_ne_C hg)).toAlgHom

theorem substitute_algebraMap (g : RatFunc K) (hg : ¬ ∃ c : K, g = RatFunc.C c)
    (p : Polynomial K) :
    substitute g hg (algebraMap (Polynomial K) (RatFunc K) p) = aeval g p := by
  simp [substitute, ← IntermediateField.aeval_coe]

theorem substitute_X (g : RatFunc K) (hg : ¬ ∃ c : K, g = RatFunc.C c) :
    substitute g hg RatFunc.X = g := by
  rw [← RatFunc.algebraMap_X, substitute_algebraMap, aeval_X]

/-- Degree of a rational function as the maximum of its normalized numerator and denominator degrees. -/
def rationalDegree (f : RatFunc K) : ℕ := max f.num.natDegree f.denom.natDegree

/-- The exact degree of f(g(X)) is the product of the two rational degrees. -/
theorem rationalDegree_substitute (f g : RatFunc K) (hg : ¬ ∃ c : K, g = RatFunc.C c) :
    rationalDegree (substitute g hg f) = rationalDegree f * rationalDegree g := by
  let E := adjoin K ({f} : Set (RatFunc K))
  let M := adjoin K ({g} : Set (RatFunc K))
  let H := adjoin K ({substitute g hg f} : Set (RatFunc K))
  let e : RatFunc K ≃ₐ[K] M :=
    RatFunc.algEquivOfTranscendental g (g.transcendental_of_ne_C hg)
  have hHM : H ≤ M := by
    refine adjoin_simple_le_iff.mpr ?_
    exact (e f).property
  letI : Algebra H M := (IntermediateField.inclusion hHM).toRingHom.toAlgebra
  letI : IsScalarTower H M (RatFunc K) := IsScalarTower.of_algebraMap_eq' rfl
  have hMap : E.map (substitute g hg) = H := by
    change (adjoin K ({f} : Set (RatFunc K))).map (substitute g hg) =
      adjoin K ({substitute g hg f} : Set (RatFunc K))
    rw [adjoin_map, Set.image_singleton]
  let i : E ≃ₐ[K] H :=
    (E.equivMap (substitute g hg)).trans (IntermediateField.equivOfEq hMap)
  have hCompat : (algebraMap H M).comp i.toRingEquiv.toRingHom =
      e.toRingEquiv.toRingHom.comp (algebraMap E (RatFunc K)) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    rfl
  have hIndex : Module.finrank E (RatFunc K) = Module.finrank H M :=
    Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv e.toRingEquiv hCompat
  have hTower := Module.finrank_mul_finrank H M (RatFunc K)
  rw [← hIndex] at hTower
  have hf : Module.finrank E (RatFunc K) = rationalDegree f := RatFunc.finrank_eq_max_natDegree
  have hg' : Module.finrank M (RatFunc K) = rationalDegree g := RatFunc.finrank_eq_max_natDegree
  have hh : Module.finrank H (RatFunc K) = rationalDegree (substitute g hg f) :=
    RatFunc.finrank_eq_max_natDegree
  rw [hf, hg', hh] at hTower
  exact hTower.symm

end

end ManuscriptAudit.RationalSubstitutionDegree

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.RationalSubstitutionDegree.substitute_algebraMap,
      ``ManuscriptAudit.RationalSubstitutionDegree.substitute_X,
      ``ManuscriptAudit.RationalSubstitutionDegree.rationalDegree_substitute] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
