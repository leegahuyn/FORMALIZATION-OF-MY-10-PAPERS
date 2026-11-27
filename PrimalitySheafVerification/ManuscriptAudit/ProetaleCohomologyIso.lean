import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology

/-! Actual native cohomology isomorphisms obtained directly by
functoriality on sheaf morphisms in the native coefficient universe. -/

namespace ManuscriptAudit.ProetaleCohomologyIso

open AlgebraicGeometry CategoryTheory
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} {F G : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}}

/-- An actual isomorphism of native coefficient sheaves induces an
additive isomorphism of the native pro-étale cohomology groups. -/
def cohomologyIso (e : F ≅ G) (n : ℕ) : Sheaf.H F n ≃+ Sheaf.H G n where
  toFun := Sheaf.H.map e.hom n
  invFun := Sheaf.H.map e.inv n
  left_inv a := by
    rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv a := by
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  map_add' a b := map_add (Sheaf.H.map e.hom n) a b

end
end ManuscriptAudit.ProetaleCohomologyIso

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleCohomologyIso.cohomologyIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
