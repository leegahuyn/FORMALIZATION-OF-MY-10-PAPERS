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
def tensorCofan : BinaryCofan (U S) (U T) :=
  BinaryCofan.mk
    (includeLeft : S →ₐ[R] S ⊗[R] T).toUnder
    (includeRight : T →ₐ[R] S ⊗[R] T).toUnder

private def algebraDesc (s : BinaryCofan (U S) (U T)) :
    S ⊗[R] T →ₐ[R] s.pt :=
  lift (CommRingCat.toAlgHom s.inl) (CommRingCat.toAlgHom s.inr)
    (fun _ _ ↦ Commute.all _ _)

private def underDesc (s : BinaryCofan (U S) (U T)) : (tensorCofan S T).pt ⟶ s.pt :=
  Under.homMk (CommRingCat.ofHom (algebraDesc S T s).toRingHom) (by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun r ↦ (algebraDesc S T s).commutes r)

set_option maxHeartbeats 2500000 in
/-- The actual tensor product is the coproduct in algebras over R. -/
def tensorIsColimit : IsColimit (tensorCofan S T) :=
  BinaryCofan.isColimitMk (underDesc S T)
    (fun s ↦ by
      apply CommRingCat.mkUnder_ext
      intro x
      change (algebraDesc S T s) (includeLeft x) = CommRingCat.toAlgHom s.inl x
      exact DFunLike.congr_fun (lift_comp_includeLeft _ _ _) x)
    (fun s ↦ by
      apply CommRingCat.mkUnder_ext
      intro x
      change (algebraDesc S T s) (includeRight x) = CommRingCat.toAlgHom s.inr x
      exact DFunLike.congr_fun (lift_comp_includeRight' _ _ _) x)
    (fun s m hL hR ↦ by
      have hm : CommRingCat.toAlgHom m = algebraDesc S T s := by
        apply Algebra.TensorProduct.ext
        · ext x
          change m.right (includeLeft x) = (algebraDesc S T s) (includeLeft x)
          calc
            _ = s.inl.right x := congrArg (fun f ↦ f.right x) hL
            _ = _ := (DFunLike.congr_fun (lift_comp_includeLeft _ _ _) x).symm
        · ext x
          change m.right (includeRight x) = (algebraDesc S T s) (includeRight x)
          calc
            _ = s.inr.right x := congrArg (fun f ↦ f.right x) hR
            _ = _ := (DFunLike.congr_fun (lift_comp_includeRight' _ _ _) x).symm
      apply CommRingCat.mkUnder_ext
      intro x
      exact DFunLike.congr_fun hm x)

/-- The canonical coproduct in algebras is isomorphic to the actual tensor. -/
def tensorIso [HasBinaryCoproduct (U S) (U T)] : (tensorCofan S T).pt ≅ U S ⨿ U T :=
  (tensorIsColimit S T).coconePointUniqueUpToIso (BinaryCofan.isColimitMk
    (fun s ↦ coprod.desc s.inl s.inr) (fun s ↦ coprod.inl_desc _ _)
    (fun s ↦ coprod.inr_desc _ _) (fun s m hm₁ hm₂ ↦
      coprod.hom_ext (hm₁.trans (coprod.inl_desc _ _).symm)
        (hm₂.trans (coprod.inr_desc _ _).symm)))

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
