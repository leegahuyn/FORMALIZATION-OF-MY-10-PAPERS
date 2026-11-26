import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Degree-two dimension shifting for actual abelian sheaves

For a short exact sequence with injective middle sheaf, the connecting
homomorphism identifies the degree-one cohomology of the quotient with
the degree-two cohomology of the kernel.
-/

namespace ManuscriptAudit.SheafCohomologyDimensionShift

open CategoryTheory CategoryTheory.Abelian

universe u v w w'

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- The native connecting map is an additive equivalence when the middle sheaf is injective. -/
def hOneQuotientEquivHTwo (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (hS : S.ShortExact) [Injective S.X₂] :
    Sheaf.H S.X₃ 1 ≃+ Sheaf.H S.X₁ 2 := by
  let Z := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))
  let δ : Sheaf.H S.X₃ 1 →+ Sheaf.H S.X₁ 2 :=
    hS.extClass.postcomp Z (show 1 + 1 = 2 by rfl)
  have hf : Function.Injective δ := by
    intro x y hxy
    have h₀ : δ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have he := Ext.covariant_sequence_exact₃' Z hS 1 2 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at he
    obtain ⟨a, ha⟩ := (he (x - y)).mp h₀
    have ha₀ : a = 0 := Ext.eq_zero_of_injective a
    apply sub_eq_zero.mp
    change Sheaf.H.map S.g 1 a = x - y at ha
    rw [← ha, ha₀, map_zero]
  have hg : Function.Surjective δ := by
    intro x
    have hx : x.comp (Ext.mk₀ S.f) (add_zero 2) = 0 := Ext.eq_zero_of_injective _
    exact Ext.covariant_sequence_exact₁ Z hS x hx (show 1 + 1 = 2 by rfl)
  exact AddEquiv.ofBijective δ ⟨hf, hg⟩

end

end ManuscriptAudit.SheafCohomologyDimensionShift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafCohomologyDimensionShift.hOneQuotientEquivHTwo
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
