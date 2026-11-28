import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOneToPicard
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleProduct

/-! The native affine étale H¹-to-Picard comparison is an injective additive map. -/

namespace ManuscriptAudit.AffineEtaleHOnePicardAdd

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open TensorProduct AffineEtaleTensorOverlap KummerUnitsSheaf
open AffineEtaleUnitCocycle SheafSectionDifference SheafH1Descent
open AffineEtaleHOneToPicard AffineEtalePicardClass AffineEtalePicardRefinement AffineEtalePicardSameCover
open AffineEtaleFaithfullyFlatRepresentatives FaithfullyFlatCocyclePicard
open FaithfullyFlatCocycleProduct TwistedTensorEqualizer

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] doubleEtale tripleEtale KummerCohomologySequence.affineSiteHasExt

variable (R : Type) [CommRing R]

private abbrev G := coordinateUnitSheaf (Spec (CommRingCat.of R))
private abbrev terminal := KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)

variable {I : Sheaf (Scheme.AffineEtale.topology (Spec (CommRingCat.of R))) AddCommGrpCat.{0}}
variable (ι : G R ⟶ I) [Mono ι]

section Local

variable (B : Type) [CommRing B] [Algebra R B] [Algebra.Etale R B]
variable (x x' : (cokernel ι).obj.obj (op (baseObject R)))
variable (y y' : I.obj.obj (op (ofAlgebra R B)))
variable (hy : (cokernel.π ι).hom.app (op (ofAlgebra R B)) y =
  (cokernel ι).obj.map (coverArrow R B).op x)
variable (hy' : (cokernel.π ι).hom.app (op (ofAlgebra R B)) y' =
  (cokernel ι).obj.map (coverArrow R B).op x')

include hy hy' in
private theorem lift_add :
    (cokernel.π ι).hom.app (op (ofAlgebra R B)) (y + y') =
      (cokernel ι).obj.map (coverArrow R B).op (x + x') := by
  change ((cokernel.π ι).hom.app (op (ofAlgebra R B))).hom (y + y') =
    ((cokernel ι).obj.map (coverArrow R B).op).hom (x + x')
  rw [map_add, map_add]
  exact congrArg₂ (· + ·) hy hy'

private theorem transition_add :
    transition R B ι (x + x') (y + y') (lift_add R ι B x x' y y' hy hy') =
      transition R B ι x y hy * transition R B ι x' y' hy' := by
  let D := ofAlgebra R (B ⊗[R] B)
  let a : (G R).obj.obj (op D) := Additive.ofMul (transition R B ι x y hy)
  let b : (G R).obj.obj (op D) := Additive.ofMul (transition R B ι x' y' hy')
  let c : (G R).obj.obj (op D) :=
    Additive.ofMul (transition R B ι (x + x') (y + y') (lift_add R ι B x x' y y' hy hy'))
  let f := I.obj.map (firstProjection R B).op
  let g := I.obj.map (secondProjection R B).op
  have ha : ι.hom.app (op D) a = f y - g y := transition_image R B ι x y hy
  have hb : ι.hom.app (op D) b = f y' - g y' := transition_image R B ι x' y' hy'
  have hc : ι.hom.app (op D) c = f (y + y') - g (y + y') :=
    transition_image R B ι (x + x') (y + y') (lift_add R ι B x x' y y' hy hy')
  have he : c = a + b := by
    apply section_injective ι D
    calc
      ι.hom.app (op D) c = f (y + y') - g (y + y') := hc
      _ = (f y - g y) + (f y' - g y') := by
        change f.hom (y + y') - g.hom (y + y') = _
        rw [f.hom.map_add, g.hom.map_add]
        abel
      _ = ι.hom.app (op D) a + ι.hom.app (op D) b := congrArg₂ (· + ·) ha.symm hb.symm
      _ = ι.hom.app (op D) (a + b) := ((ι.hom.app (op D)).hom.map_add a b).symm
  exact congrArg (fun z : Additive (Double R B)ˣ => z.toMul) he

variable [Module.FaithfullyFlat R B]

private theorem cocycleClass_congr {t s : (Double R B)ˣ} (ht : IsCocycle R B t) (hs : IsCocycle R B s)
    (e : t = s) : picardClass R B t ht = picardClass R B s hs := by
  subst s
  rfl

private theorem picardClassOfLift_add :
    picardClassOfLift R B ι (x + x') (y + y') (lift_add R ι B x x' y y' hy hy') =
      picardClassOfLift R B ι x y hy * picardClassOfLift R B ι x' y' hy' := by
  unfold picardClassOfLift
  let t := transition R B ι x y hy
  let s := transition R B ι x' y' hy'
  exact (cocycleClass_congr R B _ (mul_isCocycle R B t s _ _) (transition_add R ι B x x' y y' hy hy')).trans
    (picardClass_mul R B t s _ _)

end Local

variable [Injective I]

/-- Addition of actual cohomology classes corresponds to tensor product
of their descended invertible modules. -/
theorem toPicard_add (h k : Sheaf.H (G R) 1) :
    toPicard R ι (h + k) = toPicard R ι h * toPicard R ι k := by
  obtain ⟨x, hx, ⟨c⟩⟩ := exists_faithfullyFlatAffineRepresentative R ι h
  obtain ⟨x', hx', ⟨c'⟩⟩ := exists_faithfullyFlatAffineRepresentative R ι k
  let B := c.coverRing
  let C := c'.coverRing
  letI : CommRing B := c.commRing
  letI : Algebra R B := c.algebra
  letI : Algebra.Etale R B := c.etale
  letI : Module.FaithfullyFlat R B := c.faithfullyFlat
  letI : CommRing C := c'.commRing
  letI : Algebra R C := c'.algebra
  letI : Algebra.Etale R C := c'.etale
  letI : Module.FaithfullyFlat R C := c'.faithfullyFlat
  let D := B ⊗[R] C
  letI : Algebra.Etale R D := Algebra.Etale.comp R B D
  letI : Module.FaithfullyFlat R D := Module.FaithfullyFlat.trans R B D
  let f : B →ₐ[R] D := Algebra.TensorProduct.includeLeft
  let g : C →ₐ[R] D := Algebra.TensorProduct.includeRight
  let yl := I.obj.map (ofAlgHom f).op c.value
  let yr := I.obj.map (ofAlgHom g).op c'.value
  let hl := refine_lifts R B D f ι x c.value c.lifts
  let hr := refine_lifts R C D g ι x' c'.value c'.lifts
  let tc (u : (cokernel ι).obj.obj (op (baseObject R))) (w : I.obj.obj (op (ofAlgebra R D)))
      (hw : (cokernel.π ι).hom.app (op (ofAlgebra R D)) w =
        (cokernel ι).obj.map (coverArrow R D).op u) : FaithfullyFlatAffineLift R ι u :=
    { coverRing := D, commRing := inferInstance, algebra := inferInstance, etale := inferInstance,
      faithfullyFlat := inferInstance, value := w, lifts := hw }
  have hsum : connectingSection ι (terminal R) (x + x') = h + k := by
    simp only [connectingSection, map_add] at hx hx' ⊢
    rw [hx, hx']
  rw [toPicard_of_representative R ι (x + x') (h + k)
        (tc (x + x') (yl + yr) (lift_add R ι D x x' yl yr hl hr)) hsum,
    toPicard_of_representative R ι x h (tc x yl hl) hx,
    toPicard_of_representative R ι x' k (tc x' yr hr) hx']
  exact picardClassOfLift_add R ι D x x' yl yr hl hr

/-- The native first unit cohomology maps additively to the actual affine Picard group. -/
def toPicardAdd : Sheaf.H (G R) 1 →+ Additive (CommRing.Pic R) where
  toFun h := Additive.ofMul (toPicard R ι h)
  map_add' h k := congrArg Additive.ofMul (toPicard_add R ι h k)
  map_zero' := congrArg Additive.ofMul (mul_left_cancel
    (show toPicard R ι 0 * toPicard R ι 0 = toPicard R ι 0 * 1 by
      simpa only [zero_add, mul_one] using (toPicard_add R ι 0 0).symm))

theorem toPicardAdd_injective : Function.Injective (toPicardAdd R ι) := by
  intro h k hk
  apply sub_eq_zero.mp
  apply eq_zero_of_toPicard_one R ι
  change toPicardAdd R ι (h - k) = 0
  rw [map_sub, hk, sub_self]

end

end ManuscriptAudit.AffineEtaleHOnePicardAdd

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleHOnePicardAdd.toPicard_add,
      ``ManuscriptAudit.AffineEtaleHOnePicardAdd.toPicardAdd,
      ``ManuscriptAudit.AffineEtaleHOnePicardAdd.toPicardAdd_injective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
