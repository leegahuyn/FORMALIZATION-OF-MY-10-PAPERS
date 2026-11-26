import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import PrimalitySheafVerification.ManuscriptAudit.CuspConductorSquare
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange

/-!
# Point neighborhoods of the rational cusp origin

The geometric fiber functor at the image of a point identifies with
the geometric fiber functor on actual pullbacks of étale neighborhoods.
The cusp specialization uses the constant-coefficient residue map of
the existing conductor square.
-/

namespace ManuscriptAudit.SmallEtaleGeometricBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SmallEtaleBaseChange

noncomputable section

universe u

variable {Z X : Scheme.{u}} (i : Z ⟶ X)
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private def geometricFiberEquiv (W : X.Etale) :
    (Scheme.pointSmallEtale s).fiber.obj ((etaleBaseChange i).obj W) ≃
      (Scheme.pointSmallEtale (s ≫ i)).fiber.obj W where
  toFun t := Over.homMk (t.left ≫ pullback.fst W.hom i) (by
    have ht : t.left ≫ pullback.snd W.hom i = s := Over.w t
    change (t.left ≫ pullback.fst W.hom i) ≫ W.hom = s ≫ i
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht])
  invFun t := Over.homMk (pullback.lift t.left s (Over.w t)) (pullback.lift_snd _ _ _)
  left_inv t := by
    have ht : t.left ≫ pullback.snd W.hom i = s := Over.w t
    apply CostructuredArrow.hom_ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd]
      exact ht.symm
  right_inv t := by
    apply CostructuredArrow.hom_ext
    exact pullback.lift_fst _ _ _

/-- Geometric point fibers commute with pullback of étale neighborhoods. -/
def geometricFiberBaseChangeIso :
    etaleBaseChange i ⋙ (Scheme.pointSmallEtale s).fiber ≅
      (Scheme.pointSmallEtale (s ≫ i)).fiber :=
  NatIso.ofComponents (fun W => (geometricFiberEquiv i s W).toIso) (fun {W Y} f => by
    ext t : 1
    apply CostructuredArrow.hom_ext
    change (t.left ≫ ((etaleBaseChange i).map f).left) ≫ pullback.fst Y.hom i =
      (t.left ≫ pullback.fst W.hom i) ≫ f.left
    simp only [etaleBaseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_fst])

variable (K : Type u) [Field K]

/-- The rational cusp origin defined by the checked conductor residue map. -/
abbrev cuspOrigin :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (CuspPunctured.CuspSubalgebra K)) :=
  Spec.map (CuspConductorSquare.origin K)

theorem cuspOrigin_closedImmersion : IsClosedImmersion (cuspOrigin K) := by
  apply IsClosedImmersion.spec_of_surjective
  intro c
  refine ⟨algebraMap K (CuspPunctured.CuspSubalgebra K) c, ?_⟩
  change (algebraMap K (Polynomial K) c).coeff 0 = c
  rw [← Polynomial.C_eq_algebraMap, Polynomial.coeff_C_zero]

variable [IsSepClosed K]

/-- The actual rational cusp origin point is the fiber of étale base change to the residue field. -/
def cuspOriginFiberIso :
    etaleBaseChange (cuspOrigin K) ⋙
        (Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of K)))).fiber ≅
      (Scheme.pointSmallEtale (cuspOrigin K)).fiber :=
  geometricFiberBaseChangeIso (cuspOrigin K) (𝟙 _) ≪≫
    eqToIso (by rw [Category.id_comp])

end

end ManuscriptAudit.SmallEtaleGeometricBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleGeometricBaseChange.geometricFiberBaseChangeIso,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.cuspOrigin_closedImmersion,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.cuspOriginFiberIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
