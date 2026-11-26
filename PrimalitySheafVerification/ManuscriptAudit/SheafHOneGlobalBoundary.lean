import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# A non-liftable global quotient section gives nonzero H¹

This transports the exact connecting map through the native
identification of H⁰ with sections at a terminal object.
-/

namespace ManuscriptAudit.SheafHOneGlobalBoundary

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

private noncomputable abbrev integerConstant : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

/-- The native connecting class of a section evaluated at a terminal object. -/
def boundaryAtTerminal (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    {T : C} (hT : IsTerminal T) (z : S.X₃.obj.obj (op T)) : Sheaf.H S.X₁ 1 :=
  hS.extClass.postcomp (integerConstant (J := J)) (show 0 + 1 = 1 by rfl)
    ((Sheaf.H.equiv₀ S.X₃ hT).symm z)

theorem boundaryAtTerminal_eq_zero_iff (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (hS : S.ShortExact) {T : C} (hT : IsTerminal T) (z : S.X₃.obj.obj (op T)) :
    boundaryAtTerminal S hS hT z = 0 ↔
      ∃ y : S.X₂.obj.obj (op T), S.g.hom.app (op T) y = z := by
  have exactness := Ext.covariant_sequence_exact₃' (integerConstant (J := J)) hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at exactness
  constructor
  · intro hc
    obtain ⟨y, hy⟩ := (exactness ((Sheaf.H.equiv₀ S.X₃ hT).symm z)).1 hc
    refine ⟨(Sheaf.H.equiv₀ S.X₂ hT) y, ?_⟩
    apply (Sheaf.H.equiv₀ S.X₃ hT).symm.injective
    rw [← Sheaf.H.equiv₀_symm_naturality (hT := hT) S.g, AddEquiv.symm_apply_apply]
    exact hy
  · rintro ⟨y, hy⟩
    apply (exactness ((Sheaf.H.equiv₀ S.X₃ hT).symm z)).2
    refine ⟨(Sheaf.H.equiv₀ S.X₂ hT).symm y, ?_⟩
    rw [Sheaf.H.equiv₀_symm_naturality (hT := hT) S.g, hy]

theorem hOne_nontrivial_of_unlifted_global_section
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    {T : C} (hT : IsTerminal T) (z : S.X₃.obj.obj (op T))
    (hz : ¬ ∃ y : S.X₂.obj.obj (op T), S.g.hom.app (op T) y = z) :
    Nontrivial (Sheaf.H S.X₁ 1) :=
  ⟨⟨boundaryAtTerminal S hS hT z, 0, fun h =>
    hz ((boundaryAtTerminal_eq_zero_iff S hS hT z).mp h)⟩⟩

