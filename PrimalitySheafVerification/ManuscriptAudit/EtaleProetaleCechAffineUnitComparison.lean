import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.QuasiIso
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleUnitBijective
import PrimalitySheafVerification.ManuscriptAudit.CechNervePreservesFiniteLimits
import PrimalitySheafVerification.ManuscriptAudit.NativeCechNerve

/-! The actual adjunction unit and the finite-limit-preserving
étale inclusion compare the two literal affine Čech complexes. -/

namespace ManuscriptAudit.EtaleProetaleCechAffineUnitComparison

open AlgebraicGeometry AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open EtaleProetaleSiteInclusion (inclusion)
open EtaleProetaleInverseImage (inverseImage adjunction)
open NativeAffineEtaleKanComparison (toNative)
open CechNerveLowDegrees (N)
open NativeCechNerve (Cech)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private abbrev L := inclusion (X (A := A))
private abbrev P := ((inverseImage (X (A := A))).obj I).obj
private abbrev η := ((adjunction (X (A := A))).unit.app I).hom

private def isoRightOp {C D : Type*} [Category* C] [Category* D] {F H : Cᵒᵖ ⥤ D}
    (e : F ≅ H) : F.rightOp ≅ H.rightOp where
  hom := e.inv.rightOp
  inv := e.hom.rightOp
  hom_inv_id := by rw [← NatTrans.rightOp_comp, Iso.hom_inv_id, NatTrans.rightOp_id]
  inv_hom_id := by rw [← NatTrans.rightOp_comp, Iso.inv_hom_id, NatTrans.rightOp_id]

variable {V W : (X (A := A)).Etale} (f : V ⟶ W)
  (hAff : ∀ n, IsAffine (N f n).left)
  (hRaw : ∀ V : (X (A := A)).ProEt, IsAffine V.left →
    Function.Bijective ((toNative (X (A := A)) I).app (op V)))

set_option maxHeartbeats 6000000 in
/-- The complex comparison keeps the actual Čech differentials. -/
def isoComplex : Cech f I.obj ≅ Cech (L.map f) (P I) := by
  let M := (Arrow.mk f).cechNerve
  let D := (Arrow.mk (L.map f)).cechNerve
  let u : M.rightOp ⋙ I.obj ⟶ M.rightOp ⋙ (L.op ⋙ P I) := Functor.whiskerLeft M.rightOp (η I)
  letI (a : SimplexCategory) : IsIso (u.app a) := by
    let V := M.obj (op a)
    letI : IsAffine V.left := hAff a.len
    have h : Function.Bijective ((u.app a).hom) := by
      change Function.Bijective ((η I).app (op V))
      exact NativeAffineEtaleUnitBijective.unit_at_affine I hRaw V
    let j := (AddEquiv.ofBijective ((u.app a).hom) h).toAddCommGrpIso
    have hj : j.hom = u.app a := AddCommGrpCat.hom_ext rfl
    rw [← hj]
    infer_instance
  letI : IsIso u := NatIso.isIso_of_isIso_app u
  let e : M ⋙ L ≅ D := CechNervePreservesFiniteLimits.comparison L f
  let j : M.rightOp ⋙ I.obj ≅ D.rightOp ⋙ P I :=
    (asIso u).trans ((Functor.associator M.rightOp L.op (P I)).symm.trans
      ((Functor.isoWhiskerRight (Functor.rightOpComp M L).symm (P I)).trans
        (Functor.isoWhiskerRight (isoRightOp e) (P I))))
  exact (alternatingCofaceMapComplex G.{u}).mapIso j

/-- Exactness is carried from the actual étale Čech complex to the
actual inverse image on any arrow between these affine étale charts. -/
theorem exactAt_of_exactAt (n : ℕ) (h : (Cech f I.obj).ExactAt n) :
    (Cech (L.map f) (P I)).ExactAt n :=
  (exactAt_iff_of_quasiIsoAt (isoComplex I f hAff hRaw).hom n).mp h

end
end ManuscriptAudit.EtaleProetaleCechAffineUnitComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleProetaleCechAffineUnitComparison.exactAt_of_exactAt
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
