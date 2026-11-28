import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Defs
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyDimensionShift

/-! Degree one of the actual sheaf is the ordinary cokernel of the
corresponding quotient arrow on global sections. -/

namespace ManuscriptAudit.SheafCohomologyHOneCokernel

open CategoryTheory CategoryTheory.Abelian

noncomputable section

section Additive

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable (g : A →+ B) (δ : B →+ C)

/-- A surjective additive boundary identifies the actual cokernel of
the preceding arrow with its codomain when exactness holds. -/
def cokernelEquiv (h : δ.ker = g.range) (hs : Function.Surjective δ) :
    (B ⧸ g.range) ≃+ C := by
  let D := QuotientAddGroup.lift g.range δ h.symm.le
  refine AddEquiv.ofBijective D ⟨(QuotientAddGroup.injective_lift_iff _ _ _).mpr h.symm, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := hs x
  exact ⟨QuotientAddGroup.mk' g.range y, hy⟩

end Additive

universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)

private abbrev Z :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

abbrev boundary : Sheaf.H S.X₃ 0 →+ Sheaf.H S.X₁ 1 :=
  hS.extClass.postcomp Z (show 0+1=1 by rfl)

theorem boundary_kernel : (boundary S hS).ker = (Sheaf.H.map S.g 0).range := by
  have he := Ext.covariant_sequence_exact₃' Z hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at he
  ext x
  exact he x

theorem boundary_surjective [Injective S.X₂] : Function.Surjective (boundary S hS) := by
  intro x
  have h : x.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
  exact Ext.covariant_sequence_exact₁ Z hS x h (show 0+1=1 by rfl)

/-- This cokernel gives the specified actual first derived cohomology. -/
def hOneEquiv [Injective S.X₂] :
    (Sheaf.H S.X₃ 0 ⧸ (Sheaf.H.map S.g 0).range) ≃+ Sheaf.H S.X₁ 1 :=
  cokernelEquiv (Sheaf.H.map S.g 0) (boundary S hS)
    (boundary_kernel S hS) (boundary_surjective S hS)

end
end ManuscriptAudit.SheafCohomologyHOneCokernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafCohomologyHOneCokernel.hOneEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
