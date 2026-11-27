import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-! The actual degree-one connecting map of a sheaf monomorphism is
additive and its zero classes are exactly the globally liftable sections. -/

namespace ManuscriptAudit.SheafCokernelBoundary

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open SheafH1Descent (connectingSection connectingSection_of_lift)

universe u v w w'
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {F I : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I) [Mono i]
  {T : C} (hT : IsTerminal T)

/-- The actual connecting map, as an additive homomorphism on sections. -/
def boundary : (cokernel i).obj.obj (op T) →+ Sheaf.H F 1 where
  toFun := connectingSection i hT
  map_zero' := by unfold connectingSection; rw [map_zero, map_zero]
  map_add' a b := by unfold connectingSection; rw [map_add, map_add]

theorem boundary_eq_zero_iff (x : (cokernel i).obj.obj (op T)) :
    boundary i hT x = 0 ↔ ∃ z : I.obj.obj (op T), (cokernel.π i).hom.app (op T) z = x := by
  constructor
  · intro hx
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact :=
      ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i),
        inferInstanceAs (Mono i), inferInstanceAs (Epi (cokernel.π i))⟩
    let Z := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))
    let x₀ := (Sheaf.H.equiv₀ (cokernel i) hT).symm x
    change (hS.extClass.postcomp Z (show 0 + 1 = 1 by rfl)) x₀ = 0 at hx
    have he := Ext.covariant_sequence_exact₃' Z hS 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at he
    obtain ⟨y, hy⟩ := (he x₀).mp hx
    refine ⟨Sheaf.H.equiv₀ I hT y, ?_⟩
    change Sheaf.H.map (cokernel.π i) 0 y = x₀ at hy
    rw [Sheaf.H.equiv₀_naturality, hy]
    exact (Sheaf.H.equiv₀ _ hT).apply_symm_apply x
  · rintro ⟨z, rfl⟩
    exact connectingSection_of_lift i hT z

end
end ManuscriptAudit.SheafCokernelBoundary

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafCokernelBoundary.boundary_eq_zero_iff
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
