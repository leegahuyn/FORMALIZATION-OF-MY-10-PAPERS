import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSheafification
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitComparison
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleRootLabelsSemilinear

/-! The identified constant root labels give a genuine commutative
square of actual sheaves for a semilinear scheme morphism. -/

namespace ManuscriptAudit.FullEtaleConstantRootLabel

open AlgebraicGeometry CategoryTheory Opposite
open KummerUnitsSheaf KummerRootLabels KummerConstantCoefficients
open OpenEtaleExtension OpenEtaleSheafification FullEtaleRootLabelsSemilinear

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}
private abbrev G (X : Scheme.{0}) := fullCoordinateUnitSheaf X
private abbrev C (X : Scheme.{0}) := constantSheaf X.smallEtaleTopology A
private abbrev P (X : Scheme.{0}) := Functor.const X.Etaleᵒᵖ
private abbrev s (X : Scheme.{0}) := sheafificationAdjunction X.smallEtaleTopology A

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
private abbrev R := restriction j A
private abbrev u := (OpenEtaleUnitComparison.restrictionIso j).hom

/-- The actual identification of the restricted constant sheaf. -/
def constantComparison (M : A) : (C U).obj M ≅ (R j).obj ((C X).obj M) :=
  (comparison j).app ((P X).obj M)

variable {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K))

private abbrev M (d : ℕ) := coefficientGroup K d

/-- Literal labeling of constant field roots inside the actual full unit sheaf. -/
def unitLabel (d : ℕ) : (C X).obj (M (K := K) d) ⟶ G X :=
  ((s X).homEquiv ((P X).obj (M (K := K) d)) (G X)).symm (label k d)

variable (k' : U ⟶ Spec (CommRingCat.of K)) (σ : K →+* K)

abbrev fieldRootMap (d : ℕ) : M (K := K) d ⟶ M (K := K) d :=
  AddCommGrpCat.ofHom (mapRoots d σ).toAdditive

/-- The full-site unit labels commute with genuine pullback and the
literal semilinear map of field roots. -/
theorem unitLabel_semilinear (h : j ≫ k = k' ≫ Spec.map (CommRingCat.ofHom σ)) (d : ℕ) :
    ((constantComparison j (M (K := K) d)).hom ≫ (R j).map (unitLabel k d)) ≫ u j =
      (C U).map (fieldRootMap σ d) ≫ unitLabel k' d := by
  let F := (P X).obj (M (K := K) d)
  let G' := (P U).obj (M (K := K) d)
  let g := (P U).map (fieldRootMap σ d)
  apply ((s U).homEquiv G' (G U)).injective
  have hL : (s U).homEquiv G' ((R j).obj (G X))
      ((constantComparison j (M (K := K) d)).hom ≫ (R j).map (unitLabel k d)) =
      (precompose j).map (label k d) :=
    comparison_postcompose j F (G X) (label k d)
  have hR : (s U).homEquiv G' (G U) (unitLabel k' d) = label k' d :=
    ((s U).homEquiv G' (G U)).apply_symm_apply (label k' d)
  rw [(s U).homEquiv_naturality_right, hL]
  change (precompose j).map (label k d) ≫ (u j).hom =
    (s U).homEquiv G' (G U)
      ((presheafToSheaf U.smallEtaleTopology A).map g ≫ unitLabel k' d)
  rw [(s U).homEquiv_naturality_left, hR]
  apply NatTrans.ext
  funext T
  apply AddCommGrpCat.ext
  intro a
  exact label_semilinear k j k' σ h d T.unop a

end

end ManuscriptAudit.FullEtaleConstantRootLabel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleConstantRootLabel.unitLabel_semilinear
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
