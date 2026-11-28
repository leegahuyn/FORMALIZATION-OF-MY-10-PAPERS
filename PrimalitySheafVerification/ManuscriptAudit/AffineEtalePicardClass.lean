import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleUnitCocycle
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleCoboundary
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology

/-! A finite faithfully flat affine representative of a unit cohomology
class gives a genuine Picard class and detects its vanishing. -/

namespace ManuscriptAudit.AffineEtalePicardClass

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open TensorProduct AffineEtaleTensorOverlap KummerUnitsSheaf
open TwistedTensorEqualizer UnitCocycleTensor AffineEtaleUnitCocycle

noncomputable section

attribute [local instance] doubleEtale tripleEtale KummerCohomologySequence.affineSiteHasExt

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]
variable [Module.FaithfullyFlat R B]

private abbrev G := coordinateUnitSheaf (Spec (CommRingCat.of R))

variable {I : Sheaf (Scheme.AffineEtale.topology (Spec (CommRingCat.of R))) AddCommGrpCat.{0}}
variable (ι : G R ⟶ I) [Mono ι]
variable (x : (cokernel ι).obj.obj (op (baseObject R)))
variable (y : I.obj.obj (op (ofAlgebra R B)))
variable (hy : (cokernel.π ι).hom.app (op (ofAlgebra R B)) y =
  (cokernel ι).obj.map (coverArrow R B).op x)

private theorem face01_eq_pull12 (z : B ⊗[R] B) :
    face01 R B z = pull12 R B z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
    simp [pull12, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeft_apply]
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem face02_eq_pull13 (z : B ⊗[R] B) :
    face02 R B z = pull13 R B z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => rw [face02_tmul, pull13_tmul]
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem transition_isCocycle :
    IsCocycle R B (transition R B ι x y hy) := by
  change face02 R B _ = face12 R B _ * face01 R B _
  rw [face02_eq_pull13, face01_eq_pull12]
  change pull13 R B _ = pull23 R B _ * pull12 R B _
  rw [mul_comm]
  exact (transition_cocycle R B ι x y hy).symm

/-- A local representative of the real derived H¹ units class determines
an invertible-module class in the actual affine Picard group. -/
def picardClassOfLift : CommRing.Pic R :=
  FaithfullyFlatCocyclePicard.picardClass R B (transition R B ι x y hy)
    (transition_isCocycle R B ι x y hy)

/-- If that Picard class is trivial, the global cokernel section genuinely lifts,
so the represented derived cohomology class vanishes. -/
theorem connectingSection_eq_zero_of_picard_one (h : picardClassOfLift R B ι x y hy = 1) :
    SheafH1Descent.connectingSection ι
      (KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)) x = 0 := by
  let u := transition R B ι x y hy
  let l := Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toMonoidHom
  let r := Units.map (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toMonoidHom
  obtain ⟨v, hv⟩ := FaithfullyFlatCocyclePicard.exists_coboundary_of_picard_one
    R B u (transition_isCocycle R B ι x y hy) h
  let b : Additive Bˣ := Additive.ofMul v⁻¹
  have hb : Additive.ofMul u =
      (G R).obj.map (firstProjection R B).op b - (G R).obj.map (secondProjection R B).op b := by
    apply Additive.ext
    change u = l v⁻¹ / r v⁻¹
    rw [map_inv, map_inv, div_eq_mul_inv, inv_inv]
    exact hv
  obtain ⟨z, hz⟩ := SheafCoboundaryLift.exists_global_lift_of_double_overlap_coboundary ι
    (coverArrow R B) (firstProjection R B) (secondProjection R B) (double_isPullback R B)
    (coverArrow_generate_mem R B) x y hy b hb
  rw [← hz]
  exact SheafH1Descent.connectingSection_of_lift ι
    (KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)) z

end

end ManuscriptAudit.AffineEtalePicardClass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtalePicardClass.picardClassOfLift,
      ``ManuscriptAudit.AffineEtalePicardClass.connectingSection_eq_zero_of_picard_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
