import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleUnitCocycle
import PrimalitySheafVerification.ManuscriptAudit.AffineEtalePicardSameCover
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleRefinement
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology

/-! The native affine étale transition cocycle is natural for refining its cover. -/

namespace ManuscriptAudit.AffineEtalePicardRefinement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AffineEtaleTensorOverlap KummerUnitsSheaf SheafSectionDifference AffineEtaleUnitCocycle
open AffineEtalePicardSameCover
open FaithfullyFlatCocycleRefinement

attribute [local instance] doubleEtale tripleEtale

noncomputable section

variable (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra.Etale R B] [Algebra.Etale R C]
variable (f : B →ₐ[R] C)

private abbrev G := coordinateUnitSheaf (Spec (CommRingCat.of R))
private abbrev U := ofAlgebra R B
private abbrev V := ofAlgebra R C
private abbrev D := ofAlgebra R (B ⊗[R] B)
private abbrev E := ofAlgebra R (C ⊗[R] C)

private theorem affineArrow_ext {U V : (Spec (CommRingCat.of R)).AffineEtale}
    {f g : U ⟶ V}
    (h : ∀ b : V.left.unop, f.left.unop.hom b = g.left.unop.hom b) : f = g := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  apply Quiver.Hom.unop_inj
  exact CommRingCat.hom_ext (RingHom.ext h)

private theorem firstSquare :
    firstProjection R C ≫ ofAlgHom f =
      ofAlgHom (Algebra.TensorProduct.map f f) ≫ firstProjection R B := by
  apply affineArrow_ext R
  intro b
  let b' : B := b
  change f b' ⊗ₜ[R] (1 : C) = Algebra.TensorProduct.map f f (b' ⊗ₜ[R] (1 : B))
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem secondSquare :
    secondProjection R C ≫ ofAlgHom f =
      ofAlgHom (Algebra.TensorProduct.map f f) ≫ secondProjection R B := by
  apply affineArrow_ext R
  intro b
  let b' : B := b
  change (1 : C) ⊗ₜ[R] f b' = Algebra.TensorProduct.map f f ((1 : B) ⊗ₜ[R] b')
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem restrictMap_comp {F : (Spec (CommRingCat.of R)).AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{0}}
    {U V W : (Spec (CommRingCat.of R)).AffineEtale}
    (r : V ⟶ U) (s : W ⟶ V) (t : F.obj (op U)) :
    F.map s.op (F.map r.op t) = F.map (s ≫ r).op t := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

variable {I : Sheaf (Scheme.AffineEtale.topology (Spec (CommRingCat.of R))) AddCommGrpCat.{0}}
variable (ι : G R ⟶ I) [Mono ι]
variable (x : (cokernel ι).obj.obj (op (baseObject R)))
variable (y : I.obj.obj (op (U R B)))
variable (hy : (cokernel.π ι).hom.app (op (U R B)) y =
  (cokernel ι).obj.map (coverArrow R B).op x)
include hy

/-- The pullback of a local lift is a lift of the same global section on the refinement. -/
theorem refine_lifts :
    (cokernel.π ι).hom.app (op (V R C)) (I.obj.map (ofAlgHom f).op y) =
      (cokernel ι).obj.map (coverArrow R C).op x := by
  rw [NatTrans.naturality_apply (cokernel.π ι).hom (ofAlgHom f).op y, hy,
    restrictMap_comp (F := (cokernel ι).obj) R (coverArrow R B) (ofAlgHom f) x]
  have hT : IsTerminal (baseObject R) :=
    KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)
  rw [hT.hom_ext (ofAlgHom f ≫ coverArrow R B) (coverArrow R C)]

/-- The transition formed from a restricted lift is the literal pullback
of its unit along the map of tensor-overlap rings. -/
theorem transition_refine :
    pull R B C f (transition R B ι x y hy) =
      transition R C ι x (I.obj.map (ofAlgHom f).op y) (refine_lifts R B C f ι x y hy) := by
  let s := ofAlgHom (Algebra.TensorProduct.map f f)
  let y' := I.obj.map (ofAlgHom f).op y
  let t := transition R B ι x y hy
  let t' := transition R C ι x y' (refine_lifts R B C f ι x y hy)
  have hB : ι.hom.app (op (D R B)) (Additive.ofMul t) =
      I.obj.map (firstProjection R B).op y - I.obj.map (secondProjection R B).op y :=
    transition_image R B ι x y hy
  have hC : ι.hom.app (op (E R C)) (Additive.ofMul t') =
      I.obj.map (firstProjection R C).op y' - I.obj.map (secondProjection R C).op y' :=
    transition_image R C ι x y' (refine_lifts R B C f ι x y hy)
  have h : (G R).obj.map s.op (Additive.ofMul t) = Additive.ofMul t' := by
    apply section_injective ι (E R C)
    have hNatural : ι.hom.app (op (E R C)) ((G R).obj.map s.op (Additive.ofMul t)) =
        I.obj.map s.op (ι.hom.app (op (D R B)) (Additive.ofMul t)) :=
      NatTrans.naturality_apply ι.hom s.op (Additive.ofMul t)
    rw [hNatural, hB, hC]
    change (I.obj.map s.op).hom (_ - _) = _
    rw [map_sub]
    change I.obj.map s.op (I.obj.map (firstProjection R B).op y) -
      I.obj.map s.op (I.obj.map (secondProjection R B).op y) =
      I.obj.map (firstProjection R C).op (I.obj.map (ofAlgHom f).op y) -
      I.obj.map (secondProjection R C).op (I.obj.map (ofAlgHom f).op y)
    rw [restrictMap_comp (F := I.obj) R (firstProjection R B) s y,
      restrictMap_comp (F := I.obj) R (secondProjection R B) s y,
      restrictMap_comp (F := I.obj) R (ofAlgHom f) (firstProjection R C) y,
      restrictMap_comp (F := I.obj) R (ofAlgHom f) (secondProjection R C) y,
      firstSquare R B C f, secondSquare R B C f]
  exact congrArg Additive.toMul h

end

end ManuscriptAudit.AffineEtalePicardRefinement

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtalePicardRefinement.refine_lifts,
      ``ManuscriptAudit.AffineEtalePicardRefinement.transition_refine] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
