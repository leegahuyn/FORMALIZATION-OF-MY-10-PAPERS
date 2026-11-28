import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.RingTheory.TensorProduct.Maps

/-! The categorical coproduct in actual algebras over the chart
is its genuine affine tensor product, with the displayed two legs. -/

namespace ManuscriptAudit.AffineStageTensorCoproduct

open CategoryTheory CategoryTheory.Limits
open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : CommRingCat.{u}} (S T : Type u) [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

private abbrev U (S : Type u) [CommRing S] [Algebra R S] := CommRingCat.mkUnder R S

/-- The two canonical tensor-product inclusions. -/
def tensorCofan : BinaryCofan (U (R := R) S) (U (R := R) T) :=
  BinaryCofan.mk
    (includeLeft : S →ₐ[R] S ⊗[R] T).toUnder
    (includeRight : T →ₐ[R] S ⊗[R] T).toUnder

private abbrev rL : CommRingCat.of S ⟶ CommRingCat.of (S ⊗[R] T) :=
  CommRingCat.ofHom (includeLeftRingHom : S →+* S ⊗[R] T)

private abbrev rR : CommRingCat.of T ⟶ CommRingCat.of (S ⊗[R] T) :=
  CommRingCat.ofHom ((includeRight : T →ₐ[R] S ⊗[R] T).toRingHom)

private theorem isPushout :
    IsPushout (U (R := R) S).hom (U (R := R) T).hom (rL (R := R) S T) (rR (R := R) S T) :=
  CommRingCat.isPushout_tensorProduct R S T

private def ringDesc (s : BinaryCofan (U (R := R) S) (U (R := R) T)) :
    CommRingCat.of (S ⊗[R] T) ⟶ s.pt.right :=
  (isPushout (R := R) S T).desc s.inl.right s.inr.right
    ((Under.w s.inl).trans (Under.w s.inr).symm)

private theorem ringDesc_left (s : BinaryCofan (U (R := R) S) (U (R := R) T)) :
    rL (R := R) S T ≫ ringDesc (R := R) S T s = s.inl.right :=
  (isPushout (R := R) S T).inl_desc _ _ _

private theorem ringDesc_right (s : BinaryCofan (U (R := R) S) (U (R := R) T)) :
    rR (R := R) S T ≫ ringDesc (R := R) S T s = s.inr.right :=
  (isPushout (R := R) S T).inr_desc _ _ _

private def underDesc (s : BinaryCofan (U (R := R) S) (U (R := R) T)) :
    (tensorCofan (R := R) S T).pt ⟶ s.pt :=
  Under.homMk (ringDesc (R := R) S T s) (by
    have hl : (U (R := R) S).hom ≫ rL (R := R) S T = (tensorCofan (R := R) S T).pt.hom :=
      Under.w (tensorCofan (R := R) S T).inl
    calc
      _ = ((U (R := R) S).hom ≫ rL (R := R) S T) ≫ ringDesc (R := R) S T s :=
        congrArg (fun m ↦ m ≫ ringDesc (R := R) S T s) hl.symm
      _ = (U (R := R) S).hom ≫ s.inl.right := by
        rw [Category.assoc, ringDesc_left]
      _ = _ := Under.w s.inl)

set_option maxHeartbeats 3500000 in
/-- The actual tensor product is the coproduct in algebras over R. -/
def tensorIsColimit : IsColimit (tensorCofan (R := R) S T) :=
  BinaryCofan.isColimitMk (underDesc (R := R) S T)
    (fun s ↦ by
      apply (Under.forget R).map_injective
      exact ringDesc_left (R := R) S T s)
    (fun s ↦ by
      apply (Under.forget R).map_injective
      exact ringDesc_right (R := R) S T s)
    (fun s m hL hR ↦ by
      apply (Under.forget R).map_injective
      change m.right = ringDesc (R := R) S T s
      apply (isPushout (R := R) S T).hom_ext
      · have h : rL (R := R) S T ≫ m.right = s.inl.right :=
          congrArg (Under.forget R).map hL
        exact h.trans (ringDesc_left (R := R) S T s).symm
      · have h : rR (R := R) S T ≫ m.right = s.inr.right :=
          congrArg (Under.forget R).map hR
        exact h.trans (ringDesc_right (R := R) S T s).symm)

/-- The canonical coproduct in algebras is isomorphic to the actual tensor. -/
def tensorIso [HasBinaryCoproduct (U (R := R) S) (U (R := R) T)] :
    (tensorCofan (R := R) S T).pt ≅ U (R := R) S ⨿ U (R := R) T :=
  (tensorIsColimit (R := R) S T).coconePointUniqueUpToIso (colimit.isColimit _)

end
end ManuscriptAudit.AffineStageTensorCoproduct

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineStageTensorCoproduct.tensorIsColimit
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
