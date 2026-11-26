import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionQuotient

/-!
# Exactness of the native nested-open cokernel sequence

The exactness argument is the abelian cokernel sequence of the
monomorphism given by the actual nested-open map.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

private theorem shortExactCokernelOfMono {D : Type*} [Category* D] [Abelian D]
    {A B : D} (f : A ⟶ B) (hf : Mono f) : (ShortComplex.cokernelSequence f).ShortExact := by
  letI : Mono f := hf
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f)
    (inferInstanceAs (Mono f)) (inferInstanceAs (Epi (cokernel.π f)))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 8192 in
set_option backward.isDefEq.respectTransparency true in
/-- The actual quotient sequence of nested extension-by-zero maps is short exact. -/
theorem nestedOpenQuotientSequence_shortExact {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (M : AddCommGrpCat.{u}) :
    (nestedOpenQuotientSequence i j M).ShortExact := by
  let D := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let A : D := (extensionByZero (i ≫ j) AddCommGrpCat.{u}).obj
    ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u}).obj M)
  let B : D := (extensionByZero j AddCommGrpCat.{u}).obj
    ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u}).obj M)
  let f : A ⟶ B := nestedOpenConstantMap i j M
  have hf : Mono f := nestedOpenConstantMap_mono i j M
  let proveExact : ∀ g : A ⟶ B, Mono g → (ShortComplex.cokernelSequence g).ShortExact :=
    fun g hg => shortExactCokernelOfMono (D := D) (A := A) (B := B) g hg
  exact proveExact f hf

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotientSequence_shortExact
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
