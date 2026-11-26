import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CokernelPushout
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-!
# A degree-one class killed by a pushed-out lift

The native Ext connecting class is natural for the canonical map of
cokernel sequences. A terminal section lifting in the pushout therefore
maps to zero on degree-one cohomology.
-/

namespace ManuscriptAudit.SheafHOnePushout

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable {F I F' : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I) [Mono i] (r : F ⟶ F')

set_option backward.isDefEq.respectTransparency false in
/-- A section lifting through the pushed-out sequence has zero image
under the corresponding map on degree-one cohomology. -/
theorem map_connecting_eq_zero_of_lift {T : C} (hT : IsTerminal T)
    (x : (cokernel i).obj.obj (op T))
    (y : (pushout i r).obj.obj (op T))
    (hy : (CokernelPushout.sequence i r).g.hom.app (op T) y = x) :
    Sheaf.H.map r 1 (SheafH1Descent.connectingSection i hT x) = 0 := by
  let S := ShortComplex.cokernelSequence i
  let S' := CokernelPushout.sequence i r
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
      (inferInstanceAs (Mono i)) (inferInstanceAs (Epi (cokernel.π i)))
  have hS' : S'.ShortExact := CokernelPushout.sequence_shortExact i r
  let Z := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))
  let α : Sheaf.H (cokernel i) 0 := (Sheaf.H.equiv₀ (cokernel i) hT).symm x
  let β : Sheaf.H (pushout i r) 0 := (Sheaf.H.equiv₀ (pushout i r) hT).symm y
  have hα : Sheaf.H.map S'.g 0 β = α := by
    apply (Sheaf.H.equiv₀ (cokernel i) hT).injective
    rw [Sheaf.H.equiv₀_naturality]
    simpa only [α, β, AddEquiv.apply_symm_apply] using hy
  have hExact := Ext.covariant_sequence_exact₃' Z hS' 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExact
  have hz := (hExact α).mpr ⟨β, hα⟩
  change α.comp hS'.extClass (show 0 + 1 = 1 by rfl) = 0 at hz
  have hn := ShortComplex.ShortExact.extClass_naturality hS hS'
    (CokernelPushout.comparison i r)
  change hS.extClass.comp (Ext.mk₀ r) (add_zero 1) =
    (Ext.mk₀ (𝟙 (cokernel i))).comp hS'.extClass (zero_add 1) at hn
  change (α.comp hS.extClass (show 0 + 1 = 1 by rfl)).comp (Ext.mk₀ r) (add_zero 1) = 0
  rw [Ext.comp_assoc_of_third_deg_zero, hn, Ext.mk₀_id_comp]
  exact hz

end ManuscriptAudit.SheafHOnePushout

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafHOnePushout.map_connecting_eq_zero_of_lift
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
