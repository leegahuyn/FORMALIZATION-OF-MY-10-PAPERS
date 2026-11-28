import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtension
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeCoefficients
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-! Full-site labeling of coefficient roots and the genuine action of a
semilinear morphism on those labels, before sheafification. -/

namespace ManuscriptAudit.FullEtaleRootLabelsSemilinear

open AlgebraicGeometry CategoryTheory Opposite
open OpenEtaleExtension KummerUnitsSheaf KummerRootLabels KummerConstantCoefficients

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {X : Scheme.{0}}
variable (k : X ⟶ Spec (CommRingCat.of K))

private abbrev B := CommRingCat.of K
private abbrev c := Scheme.ΓSpecIso (B (K := K))

/-- Actual field coefficients in the global ring of any small étale object. -/
def coefficient (T : X.Etale) : B (K := K) ⟶ Γ(T.left, ⊤) :=
  c.inv ≫ (T.hom ≫ k).appTop

theorem coefficient_natural {T V : X.Etale} (f : T ⟶ V) :
    coefficient k V ≫ f.left.appTop = coefficient k T := by
  unfold coefficient
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, ← Category.assoc,
    MorphismProperty.Over.w f]

/-- The literal inclusion of roots from the coefficient field into
regular units is natural in all objects of the full small site. -/
def label (d : ℕ) :
    (Functor.const X.Etaleᵒᵖ).obj (coefficientGroup K d) ⟶ fullCoordinateUnits X where
  app T := AddCommGrpCat.ofHom (rootsOfUnity d K).subtype.toAdditive ≫
    ringUnits.map (coefficient k T.unop)
  naturality {T V} f := by
    change 𝟙 _ ≫ (AddCommGrpCat.ofHom (rootsOfUnity d K).subtype.toAdditive ≫
      ringUnits.map (coefficient k V.unop)) =
      (AddCommGrpCat.ofHom (rootsOfUnity d K).subtype.toAdditive ≫
        ringUnits.map (coefficient k T.unop)) ≫ ringUnits.map f.unop.left.appTop
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp, coefficient_natural]

variable {U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (k' : U ⟶ Spec (CommRingCat.of K)) (s : K →+* K)

private theorem coefficient_base :
    c.inv ≫ (Spec.map (CommRingCat.ofHom s)).appTop = CommRingCat.ofHom s ≫ c.inv := by
  apply (cancel_mono c.hom).mp
  rw [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- On each actual object, the map on coefficient-ring labels is exactly
the specified ground-field semilinearity. -/
theorem coefficient_semilinear (h : j ≫ k = k' ≫ Spec.map (CommRingCat.ofHom s))
    (T : U.Etale) :
    coefficient k ((etalePostcompose j).obj T) =
      CommRingCat.ofHom s ≫ coefficient k' T := by
  change c.inv ≫ ((T.hom ≫ j) ≫ k).appTop =
    CommRingCat.ofHom s ≫ c.inv ≫ (T.hom ≫ k').appTop
  rw [Category.assoc, h, ← Category.assoc, Scheme.Hom.comp_appTop,
    ← Category.assoc, coefficient_base, Category.assoc]

/-- The genuine labeled root of unity on the postcomposed étale object
equals the label of its actual field-semilinear image. -/
theorem label_semilinear (h : j ≫ k = k' ≫ Spec.map (CommRingCat.ofHom s))
    (d : ℕ) (T : U.Etale) (a : Additive (rootsOfUnity d K)) :
    (label k d).app (op ((etalePostcompose j).obj T)) a =
      (label k' d).app (op T) (Additive.ofMul (mapRoots d s a.toMul)) := by
  apply Additive.ext
  apply Units.ext
  change (coefficient k ((etalePostcompose j).obj T)).hom (a.toMul.val : K) =
    (coefficient k' T).hom (s (a.toMul.val : K))
  rw [coefficient_semilinear k j k' s h T]
  rfl

end

end ManuscriptAudit.FullEtaleRootLabelsSemilinear

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FullEtaleRootLabelsSemilinear.coefficient_natural,
      ``ManuscriptAudit.FullEtaleRootLabelsSemilinear.coefficient_semilinear,
      ``ManuscriptAudit.FullEtaleRootLabelsSemilinear.label_semilinear] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
