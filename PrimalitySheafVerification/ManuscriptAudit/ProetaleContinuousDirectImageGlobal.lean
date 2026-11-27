import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps

/-! Global sections of the actual continuous-coefficient direct image
are continuous functions on the total scheme, with its actual restriction. -/

namespace ManuscriptAudit.ProetaleContinuousDirectImageGlobal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
variable {Y Z : Scheme.{0}} (p : Y ⟶ Z)

abbrev finalObject (Z : Scheme.{0}) : Z.ProEt := Scheme.ProEt.mk (𝟙 Z)

private abbrev projection := pullback.snd (𝟙 Z) p
private abbrev slot := pullback (𝟙 Z) p

/-- Evaluate a direct image at the actual terminal object. -/
def terminalEquiv :
    (functionsOver M p).obj.obj (op (finalObject Z)) ≃+ C(Y, M) where
  toFun a := (a.down : C(slot p, M)).comp ⟨inv (projection p), (inv (projection p)).continuous⟩
  invFun a := ⟨a.comp ⟨projection p, (projection p).continuous⟩⟩
  left_inv a := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    let a' : C(slot p, M) := a.down
    change a' ((projection p ≫ inv (projection p)) x) = a' x
    rw [IsIso.hom_inv_id]
    rfl
  right_inv a := by
    apply ContinuousMap.ext
    intro x
    change a ((inv (projection p) ≫ projection p) x) = a x
    rw [IsIso.inv_hom_id]
    rfl
  map_add' _ _ := rfl

variable {O : Scheme.{0}} (q : O ⟶ Z) (g : O ⟶ Y) (hg : g ≫ p = q)

private theorem terminal_map :
    inv (projection q) ≫ pullbackMap (𝟙 Z) g hg = g ≫ inv (projection p) := by
  apply (cancel_mono (projection p)).mp
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  change inv (projection q) ≫ pullbackMap (𝟙 Z) g hg ≫ pullback.snd (𝟙 Z) p = g
  rw [pullbackMap_snd, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Actual direct-image restriction at the terminal object is
precomposition with the given morphism of total schemes. -/
theorem terminalEquiv_restriction (a : (functionsOver M p).obj.obj (op (finalObject Z))) :
    terminalEquiv M q ((restriction M g hg).hom.app (op (finalObject Z)) a) =
      (terminalEquiv M p a).comp ⟨g, g.continuous⟩ := by
  apply ContinuousMap.ext
  intro x
  let a' : C(slot p, M) := a.down
  change a' ((inv (projection q) ≫ pullbackMap (𝟙 Z) g hg) x) =
    a' ((g ≫ inv (projection p)) x)
  rw [terminal_map p q g hg]

/-- The same identification in actual native degree-zero cohomology. -/
def HZeroEquiv : Sheaf.H (functionsOver M p) 0 ≃+ C(Y, M) :=
  (Sheaf.H.equiv₀ _ (MorphismProperty.Over.mkIdTerminal @WeaklyEtale Z)).trans (terminalEquiv M p)

theorem HZeroEquiv_restriction (a : Sheaf.H (functionsOver M p) 0) :
    HZeroEquiv M q (Sheaf.H.map (restriction M g hg) 0 a) =
      (HZeroEquiv M p a).comp ⟨g, g.continuous⟩ := by
  change terminalEquiv M q ((Sheaf.H.equiv₀ _
    (MorphismProperty.Over.mkIdTerminal @WeaklyEtale Z))
      (Sheaf.H.map (restriction M g hg) 0 a)) = _
  rw [← Sheaf.H.equiv₀_naturality]
  exact terminalEquiv_restriction M p q g hg _

end
end ManuscriptAudit.ProetaleContinuousDirectImageGlobal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleContinuousDirectImageGlobal.terminalEquiv_restriction,
      ``ManuscriptAudit.ProetaleContinuousDirectImageGlobal.HZeroEquiv_restriction] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
