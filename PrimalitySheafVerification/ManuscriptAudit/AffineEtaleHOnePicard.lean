import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCocycleRepresentative
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOnePicardAdd
import PrimalitySheafVerification.ManuscriptAudit.AffineInvertibleLineSplitCover
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.SplitAffineLineCocycle

/-! The actual derived first étale unit cohomology of an affine scheme is its Picard group. -/

namespace ManuscriptAudit.AffineEtaleHOnePicard

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open TensorProduct AffineEtaleTensorOverlap KummerUnitsSheaf UnitCocycleTensor
open TwistedTensorEqualizer FlatTwistedDescentLine FaithfullyFlatCocyclePicard
open AffineEtaleFaithfullyFlatRepresentatives AffineEtaleHOnePicardAdd
open AffineEtaleHOneToPicard AffineEtalePicardClass AffineEtaleUnitCocycle

noncomputable section

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

variable (R : Type) [CommRing R]

private abbrev X := Spec (CommRingCat.of R)
private abbrev J := Scheme.AffineEtale.topology (X R)
private abbrev G := coordinateUnitSheaf (X R)
private abbrev terminal := KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)

variable {I : Sheaf (J R) AddCommGrpCat.{0}} [Injective I]
variable (ι : G R ⟶ I) [Mono ι]

private theorem tensorCocycle (B : Type) [CommRing B] [Algebra R B]
    (t : (Double R B)ˣ) (ht : IsCocycle R B t) :
    pull12 R B (t : Double R B) * pull23 R B (t : Double R B) = pull13 R B (t : Double R B) := by
  have h12 (z : Double R B) : face01 R B z = pull12 R B z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp [pull12, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeft_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h13 (z : Double R B) : face02 R B z = pull13 R B z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => rw [face02_tmul, pull13_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  change face02 R B (t : Double R B) = face12 R B (t : Double R B) * face01 R B (t : Double R B) at ht
  rw [h12, h13, mul_comm] at ht
  exact ht.symm

private theorem unitClassCongr (B : Type) [CommRing B] [Algebra R B] [Module.FaithfullyFlat R B]
    {t s : (Double R B)ˣ} (ht : IsCocycle R B t) (hs : IsCocycle R B s) (h : t = s) :
    picardClass R B t ht = picardClass R B s hs := by
  subst s
  rfl

/-- Every actual affine Picard class comes from the genuine first unit cohomology. -/
theorem toPicard_surjective : Function.Surjective (toPicard R ι) := by
  intro P
  let M := CommRing.Pic.AsModule P
  obtain ⟨c⟩ := AffineInvertibleLineSplitCover.exists_splitCover R M
  let B := c.ring
  letI : CommRing B := c.commRing
  letI : Algebra R B := c.algebra
  letI : Algebra.Etale R B := c.etale
  letI : Module.FaithfullyFlat R B := c.faithfullyFlat
  let t := SplitAffineLineCocycle.transitionUnit R B M c.trivialization
  let ht := SplitAffineLineCocycle.transitionUnit_isCocycle R B M c.trivialization
  obtain ⟨x, y, hy, hTransition⟩ :=
    AffineEtaleCocycleRepresentative.exists_representative_of_cocycle R B ι t (tensorCocycle R B t ht)
  let l : FaithfullyFlatAffineLift R ι x :=
    { coverRing := B, commRing := inferInstance, algebra := inferInstance, etale := inferInstance,
      faithfullyFlat := inferInstance, value := y, lifts := hy }
  let h := SheafH1Descent.connectingSection ι (terminal R) x
  refine ⟨h, (toPicard_of_representative R ι x h l rfl).trans ?_⟩
  change picardClassOfLift R B ι x y hy = P
  unfold picardClassOfLift
  refine (unitClassCongr R B _ ht hTransition).trans ?_
  letI : Module.Invertible R (invariants R B t) := invariants_invertible R B t ht
  have hM : CommRing.Pic.mk R (invariants R B t) = CommRing.Pic.mk R M :=
    CommRing.Pic.mk_eq_mk_iff.mpr ⟨(SplitAffineLineCocycle.invariantsEquiv R B M c.trivialization).symm⟩
  exact hM.trans (CommRing.Pic.mk_eq_self (M := P))

/-- Genuine derived coordinate-unit cohomology of the affine étale site
identifies additively with the actual affine Picard group. -/
def affineHOneEquiv : Sheaf.H (G R) 1 ≃+ Additive (CommRing.Pic R) := by
  let C := Sheaf (J R) AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology (X R) AddCommGrpCat.{0}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{0} (C := C)
  let I : C := Injective.under (G R)
  let i : G R ⟶ I := Injective.ι (G R)
  letI : Injective I := inferInstance
  letI : Mono i := inferInstance
  refine AddEquiv.ofBijective (toPicardAdd R i) ⟨toPicardAdd_injective R i, ?_⟩
  intro P
  obtain ⟨h, hh⟩ := toPicard_surjective R i P.toMul
  exact ⟨h, congrArg Additive.ofMul hh⟩

/-- The same genuine Picard identification holds on the full small étale site. -/
def fullHOneEquiv :
    Sheaf.H (fullCoordinateUnitSheaf (X R)) 1 ≃+ Additive (CommRing.Pic R) := by
  let e := ((Sheaf.functorH (J R) 1).mapIso (coordinateUnitSheafIso (X R))).addCommGroupIsoToAddEquiv
  exact (unitCohomologyEquiv (CommRingCat.of R) 1).symm.trans (e.symm.trans (affineHOneEquiv R))

end

end ManuscriptAudit.AffineEtaleHOnePicard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleHOnePicard.toPicard_surjective,
      ``ManuscriptAudit.AffineEtaleHOnePicard.affineHOneEquiv,
      ``ManuscriptAudit.AffineEtaleHOnePicard.fullHOneEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
