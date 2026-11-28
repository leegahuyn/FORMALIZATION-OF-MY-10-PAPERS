import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspRelativePowerCartesian
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCartesianChartIso
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeFreeSquarePullback

/-! The actual cusp two-chart boundary is functorial under relative power. -/

namespace ManuscriptAudit.CuspNativeRelativePowerBoundary

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspRelativePowerMap (projectiveMap affineMap lineMap affine_projectiveMap line_projectiveMap)
open CuspRelativePowerCartesian (affine_isPullback line_isPullback overlap_isPullback
  overlapEndomorphism overlapEndomorphism_fst overlapEndomorphism_snd)
open ProetaleMayerVietorisSite (siteEquivalence sheafEquivalence topology coverComplex
  coverComplex_shortExact openCoverSquare)
open ProetaleOpenLocalLifts (identityObject openObject openArrow)
open ProetaleInverseImage (inverseImage)
open ProetaleCartesianChartIso (chartIso chartIso_naturality)
open ProetaleSchemeFreeSquarePullback (free)
open SquareShortComplexTransport (ofSquare)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev P := Sheaf (Scheme.ProEt.topology (X K)) A
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev l := overlapOpen K

private abbrev square : Square (X K).ProEt where
  f₁₂ := fstLeg K
  f₁₃ := sndLeg K
  f₂₄ := openArrow (j K)
  f₃₄ := openArrow (k K)
  fac := (overlap K).w

abbrev complex := coverComplex (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)

private theorem complex_shortExact : (complex K).ShortExact :=
  coverComplex_shortExact (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)

private abbrev highFree :
    AsSmall.{1} (X K).ProEt ⥤ Sheaf (topology (X K)) A :=
  yoneda ⋙ (Functor.whiskeringRight (AsSmall.{1} (X K).ProEt)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (topology (X K)) A

set_option maxHeartbeats 5500000 in
private def complexIso : complex K ≅ ofSquare ((square K).map (free (X K))) := by
  let E := (sheafEquivalence (X K)).inverse
  letI : E.Additive := E.additive_of_preserves_binary_products
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts E
  let Q := openCoverSquare (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
  exact SquareShortComplexTransport.mapIso E (Q.toSquare.map (highFree K))

private theorem open_hom {V T : Scheme.{0}} (g : V ⟶ T) [IsOpenImmersion g] :
    (openObject g).hom = g := by
  change 𝟙 V ≫ g = g
  exact Category.id_comp _

variable (m : ℕ) (hm : 2 ≤ m)

private abbrev f := projectiveMap K m hm

private theorem affSquare :
    IsPullback (affineMap K m hm) (openObject (j K)).hom (openObject (j K)).hom (f K m hm) := by
  simpa only [open_hom] using affine_isPullback K m hm

private theorem lineSquare :
    IsPullback (lineMap K m) (openObject (k K)).hom (openObject (k K)).hom (f K m hm) := by
  simpa only [open_hom] using line_isPullback K m hm

private theorem overlapSquare :
    IsPullback (overlapEndomorphism K m) (openObject (l K)).hom (openObject (l K)).hom (f K m hm) := by
  simpa only [open_hom] using overlap_isPullback K m hm

private theorem terminalSquare :
    IsPullback (f K m hm) (identityObject (X K)).hom (identityObject (X K)).hom (f K m hm) :=
  IsPullback.of_id_snd

set_option maxHeartbeats 6500000 in
/-- The literal native cover complex is preserved by the relative power inverse image. -/
def comparison : (complex K).map (inverseImage (f K m hm)) ≅ complex K := by
  let g := f K m hm
  let h₁ := overlapSquare K m hm
  let h₂ := affSquare K m hm
  let h₃ := lineSquare K m hm
  let h₄ := terminalSquare K m hm
  refine (inverseImage g).mapShortComplex.mapIso (complexIso K) ≪≫
    ProetaleSchemeFreeSquarePullback.comparison g (square K) (square K)
      (chartIso g h₁) (chartIso g h₂) (chartIso g h₃) (chartIso g h₄) ?_ ?_ ?_ ?_ ≪≫
    (complexIso K).symm
  · exact chartIso_naturality g h₁ h₂ (fstLeg K) (fstLeg K) (overlapEndomorphism_fst K m hm).symm
  · exact chartIso_naturality g h₁ h₃ (sndLeg K) (sndLeg K) (overlapEndomorphism_snd K m).symm
  · exact chartIso_naturality g h₂ h₄ (openArrow (j K)) (openArrow (j K))
      (affine_projectiveMap K m hm)
  · exact chartIso_naturality g h₃ h₄ (openArrow (k K)) (openArrow (k K))
      (line_projectiveMap K m hm)

/-- The native Mayer–Vietoris connecting map commutes with actual relative power pullback. -/
theorem map_boundary (F : P K) (n : ℕ) (x : Ext (complex K).X₁ F n) :
    let h := complex_shortExact K
    let φ := (comparison K m hm).inv
    (Ext.mk₀ φ.τ₃).comp ((h.extClass.comp x (Nat.add_comm 1 n)).mapExactFunctor
      (inverseImage (f K m hm))) (zero_add (n + 1)) =
    h.extClass.comp ((Ext.mk₀ φ.τ₁).comp (x.mapExactFunctor (inverseImage (f K m hm))) (zero_add n))
      (Nat.add_comm 1 n) :=
  ExtContravariantBoundaryMap.map_boundary (inverseImage (f K m hm))
    (complex_shortExact K) (complex_shortExact K) (comparison K m hm).inv n x

end
end ManuscriptAudit.CuspNativeRelativePowerBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNativeRelativePowerBoundary.comparison,
      ``ManuscriptAudit.CuspNativeRelativePowerBoundary.map_boundary] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
