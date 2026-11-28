import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleFaithfullyFlatRepresentatives
import PrimalitySheafVerification.ManuscriptAudit.AffineEtalePicardClass
import PrimalitySheafVerification.ManuscriptAudit.AffineEtalePicardRefinement
import PrimalitySheafVerification.ManuscriptAudit.AffineEtalePicardSameCover
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleChangeUnit
import PrimalitySheafVerification.ManuscriptAudit.SheafH1ConnectingExact

/-!
# Actual first étale unit cohomology classes in the affine Picard group

A finite faithfully flat representative produces a descended affine line.
The tensor-product common refinement and change-of-unit calculation make
its Picard class independent of that representative.
-/

namespace ManuscriptAudit.AffineEtaleHOneToPicard

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open TensorProduct AffineEtaleTensorOverlap KummerUnitsSheaf
open AffineEtaleFaithfullyFlatRepresentatives AffineEtalePicardClass AffineEtalePicardRefinement
open AffineEtalePicardSameCover SheafH1Descent SheafH1ConnectingExact
open FaithfullyFlatCocyclePicard FaithfullyFlatCocycleRefinement
open AffineEtaleUnitCocycle TwistedTensorEqualizer

noncomputable section

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

variable (R : Type) [CommRing R]

private abbrev G := coordinateUnitSheaf (Spec (CommRingCat.of R))

private abbrev terminal := KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)

variable {I : Sheaf (Scheme.AffineEtale.topology (Spec (CommRingCat.of R))) AddCommGrpCat.{0}}
variable (ι : G R ⟶ I) [Mono ι]

private theorem picardClass_congr {B : Type} [CommRing B] [Algebra R B] [Module.FaithfullyFlat R B]
    {t t' : (Double R B)ˣ} (ht : IsCocycle R B t) (ht' : IsCocycle R B t') (h : t = t') :
    picardClass R B t ht = picardClass R B t' ht' := by
  subst t'
  rfl

section Local

variable (B C : Type) [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
variable [Algebra.Etale R B] [Algebra.Etale R C]
variable [Module.FaithfullyFlat R B] [Module.FaithfullyFlat R C]
variable (x x' : (cokernel ι).obj.obj (op (baseObject R)))
variable (y : I.obj.obj (op (ofAlgebra R B)))
variable (hy : (cokernel.π ι).hom.app (op (ofAlgebra R B)) y =
  (cokernel ι).obj.map (coverArrow R B).op x)

theorem picardClassOfLift_same_cover (y' : I.obj.obj (op (ofAlgebra R B)))
    (hy' : (cokernel.π ι).hom.app (op (ofAlgebra R B)) y' =
      (cokernel ι).obj.map (coverArrow R B).op x')
    (hx : connectingSection ι (terminal R) x = connectingSection ι (terminal R) x') :
    picardClassOfLift R B ι x y hy = picardClassOfLift R B ι x' y' hy' := by
  have hz : connectingSection ι (terminal R) (x - x') = 0 :=
    (connectingSection_sub ι (terminal R) x x').trans (sub_eq_zero.mpr hx)
  obtain ⟨z, hz⟩ := (connectingSection_eq_zero_iff ι (terminal R) (x - x')).1 hz
  obtain ⟨v, hv⟩ := transition_changeUnit_sameCover R B ι x y hy x' y' hy' z hz
  unfold picardClassOfLift
  exact (picardClass_eq_of_unit_change R B (transition R B ι x' y' hy')
    (transition R B ι x y hy) v _ _ hv).symm

theorem picardClassOfLift_refine (f : B →ₐ[R] C) :
    picardClassOfLift R B ι x y hy =
      picardClassOfLift R C ι x (I.obj.map (ofAlgHom f).op y) (refine_lifts R B C f ι x y hy) := by
  unfold picardClassOfLift
  refine (picardClass_eq_pull R B C f _ _).trans ?_
  exact picardClass_congr R _ _ (transition_refine R B C f ι x y hy)

theorem picardClassOfLift_eq_of_connecting_eq (y' : I.obj.obj (op (ofAlgebra R C)))
    (hy' : (cokernel.π ι).hom.app (op (ofAlgebra R C)) y' =
      (cokernel ι).obj.map (coverArrow R C).op x')
    (hx : connectingSection ι (terminal R) x = connectingSection ι (terminal R) x') :
    picardClassOfLift R B ι x y hy = picardClassOfLift R C ι x' y' hy' := by
  let D := B ⊗[R] C
  letI : Algebra.Etale R D := Algebra.Etale.comp R B D
  letI : Module.FaithfullyFlat R D := Module.FaithfullyFlat.trans R B D
  let f : B →ₐ[R] D := Algebra.TensorProduct.includeLeft
  let g : C →ₐ[R] D := Algebra.TensorProduct.includeRight
  let yl := I.obj.map (ofAlgHom f).op y
  let yr := I.obj.map (ofAlgHom g).op y'
  let hl := refine_lifts R B D f ι x y hy
  let hr := refine_lifts R C D g ι x' y' hy'
  exact (picardClassOfLift_refine R ι B D x y hy f).trans
    ((picardClassOfLift_same_cover R ι D x x' yl hl yr hr hx).trans
      (picardClassOfLift_refine R ι C D x' y' hy' g).symm)

end Local

variable (x : (cokernel ι).obj.obj (op (baseObject R)))

/-- The descended Picard class associated to a particular affine representative. -/
def classOfRepresentative (c : FaithfullyFlatAffineLift R ι x) : CommRing.Pic R := by
  letI := c.commRing
  letI := c.algebra
  letI := c.etale
  letI := c.faithfullyFlat
  exact picardClassOfLift R c.coverRing ι x c.value c.lifts

theorem classOfRepresentative_eq
    (c : FaithfullyFlatAffineLift R ι x) {x' : (cokernel ι).obj.obj (op (baseObject R))}
    (c' : FaithfullyFlatAffineLift R ι x')
    (hx : connectingSection ι (terminal R) x = connectingSection ι (terminal R) x') :
    classOfRepresentative R ι x c = classOfRepresentative R ι x' c' := by
  letI := c.commRing
  letI := c.algebra
  letI := c.etale
  letI := c.faithfullyFlat
  letI := c'.commRing
  letI := c'.algebra
  letI := c'.etale
  letI := c'.faithfullyFlat
  exact picardClassOfLift_eq_of_connecting_eq R ι c.coverRing c'.coverRing
    x x' c.value c.lifts c'.value c'.lifts hx

variable [Injective I]

/-- The actual affine Picard class of a genuine first derived unit cohomology class. -/
def toPicard (h : Sheaf.H (G R) 1) : CommRing.Pic R := by
  let d := exists_faithfullyFlatAffineRepresentative R ι h
  exact classOfRepresentative R ι (Classical.choose d) (Classical.choice (Classical.choose_spec d).2)

/-- The genuine Picard image agrees with the class obtained from any local representative. -/
theorem toPicard_of_representative (h : Sheaf.H (G R) 1)
    (c : FaithfullyFlatAffineLift R ι x) (hx : connectingSection ι (terminal R) x = h) :
    toPicard R ι h = classOfRepresentative R ι x c := by
  let d := exists_faithfullyFlatAffineRepresentative R ι h
  exact classOfRepresentative_eq R ι (Classical.choose d) (Classical.choice (Classical.choose_spec d).2)
    c ((Classical.choose_spec d).1.trans hx.symm)

/-- Triviality of its actual Picard image detects vanishing of the
native first unit cohomology class. -/
theorem eq_zero_of_toPicard_one (h : Sheaf.H (G R) 1) (hp : toPicard R ι h = 1) :
    h = 0 := by
  let d := exists_faithfullyFlatAffineRepresentative R ι h
  let x := Classical.choose d
  let c := Classical.choice (Classical.choose_spec d).2
  have hx : connectingSection ι (terminal R) x = h := (Classical.choose_spec d).1
  letI := c.commRing
  letI := c.algebra
  letI := c.etale
  letI := c.faithfullyFlat
  rw [← hx]
  exact connectingSection_eq_zero_of_picard_one R c.coverRing ι x c.value c.lifts hp

end

end ManuscriptAudit.AffineEtaleHOneToPicard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleHOneToPicard.picardClassOfLift_refine,
      ``ManuscriptAudit.AffineEtaleHOneToPicard.picardClassOfLift_eq_of_connecting_eq,
      ``ManuscriptAudit.AffineEtaleHOneToPicard.toPicard,
      ``ManuscriptAudit.AffineEtaleHOneToPicard.toPicard_of_representative,
      ``ManuscriptAudit.AffineEtaleHOneToPicard.eq_zero_of_toPicard_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
