import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleRootLabelsSemilinear
import PrimalitySheafVerification.ManuscriptAudit.EtaleKummerCyclicCoordinates

/-! The full-site literal field-root label restricts to the same actual
affine étale label used in the geometric Kummer sequence. -/

namespace ManuscriptAudit.AffineEtaleRootLabelCompatibility

open AlgebraicGeometry CategoryTheory Opposite
open KummerUnitsSheaf KummerUnitsPresheaf
open FullEtaleRootLabelsSemilinear

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))

private abbrev E := Scheme.AffineEtale.Spec X

/-- The genuine full-site coefficient map becomes the literal affine
coefficient map under the global-sections isomorphism. -/
theorem coefficient_affine (T : X.AffineEtale) :
    coefficient k ((E (X := X)).obj T) ≫ (Scheme.ΓSpecIso (coordinateRing T)).hom =
      CommRingCat.ofHom (KummerRelativeCoefficients.coefficientMap k T) := by
  let f : CommRingCat.of K ⟶ coordinateRing T :=
    (Scheme.Spec.preimage (T.hom ≫ k) : T.left ⟶ op (CommRingCat.of K)).unop
  have hf : Spec.map f = T.hom ≫ k := Scheme.Spec.map_preimage _
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (T.hom ≫ k).appTop) ≫ (Scheme.ΓSpecIso (coordinateRing T)).hom = f
  rw [Category.assoc, ← hf, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- Restriction of the literal full-field root-label morphism is the
same literal label on every actual affine small étale object. -/
theorem label_affine (d : ℕ) :
    Functor.whiskerLeft (E (X := X)).op (FullEtaleRootLabelsSemilinear.label k d) ≫
      (affineRestrictionUnitsIso X).hom = EtaleKummerCyclicCoordinates.label k d := by
  apply NatTrans.ext
  funext T
  apply AddCommGrpCat.ext
  intro a
  apply Additive.ext
  apply Units.ext
  let x : rootsOfUnity d K := (show Additive (rootsOfUnity d K) from a).toMul
  change (Scheme.ΓSpecIso (coordinateRing T.unop)).hom.hom
      ((coefficient k ((E (X := X)).obj T.unop)).hom (x.val : K)) =
    KummerRelativeCoefficients.coefficientMap k T.unop (x.val : K)
  exact congrArg (fun f : CommRingCat.of K ⟶ coordinateRing T.unop => f.hom (x.val : K))
    (coefficient_affine k T.unop)

end

end ManuscriptAudit.AffineEtaleRootLabelCompatibility

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleRootLabelCompatibility.label_affine
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
