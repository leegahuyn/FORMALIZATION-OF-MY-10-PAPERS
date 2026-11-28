import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleConstantRootLabel
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitHOneComposition

/-! The semilinear map of actual constant root labels is compatible with
the genuine degree-one étale pullback. -/

namespace ManuscriptAudit.FullEtaleConstantRootHOne

open AlgebraicGeometry CategoryTheory Opposite
open KummerUnitsSheaf KummerConstantCoefficients
open OpenEtaleExtension OpenEtaleSheafification FullEtaleConstantRootLabel
open OpenEtaleDegreeOneCoefficients OpenEtaleDegreeOneComposition OpenEtaleUnitHOneComposition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}
private abbrev G (X : Scheme.{0}) := fullCoordinateUnitSheaf X
private abbrev C (X : Scheme.{0}) := constantSheaf X.smallEtaleTopology A

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
private abbrev R := restriction j A
private abbrev u := (OpenEtaleUnitComparison.restrictionIso j).hom

/-- Actual degree-one étale pullback on a constant coefficient sheaf. -/
def constantPullback (M : A) :
    Sheaf.H ((C X).obj M) 1 →+ Sheaf.H ((C U).obj M) 1 :=
  pullbackWith j (constantComparison j M).inv

/-- Constant coefficient pullback is natural in the literal coefficient map. -/
theorem constantPullback_coeff {M N : A} (f : M ⟶ N)
    (x : Sheaf.H ((C X).obj M) 1) :
    constantPullback j N (Sheaf.H.map ((C X).map f) 1 x) =
      Sheaf.H.map ((C U).map f) 1 (constantPullback j M x) := by
  have h := (comparison j).inv.naturality ((Functor.const X.Etaleᵒᵖ).map f)
  change (R j).map ((C X).map f) ≫ (constantComparison j N).inv =
    (constantComparison j M).inv ≫ (C U).map f at h
  change Sheaf.H.map (constantComparison j N).inv 1
    (pullback j ((C X).obj N) (Sheaf.H.map ((C X).map f) 1 x)) =
    Sheaf.H.map ((C U).map f) 1
      (Sheaf.H.map (constantComparison j M).inv 1 (pullback j ((C X).obj M) x))
  rw [← pullback_coeff, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, h]

variable {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K))
variable (k' : U ⟶ Spec (CommRingCat.of K)) (σ : K →+* K)

private abbrev M (d : ℕ) := coefficientGroup K d

private theorem label_transport (h : j ≫ k = k' ≫ Spec.map (CommRingCat.ofHom σ)) (d : ℕ) :
    (R j).map (unitLabel k d) ≫ u j =
      (constantComparison j (M (K := K) d)).inv ≫ (C U).map (fieldRootMap σ d) ≫ unitLabel k' d := by
  apply (cancel_epi (constantComparison j (M (K := K) d)).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using unitLabel_semilinear j k k' σ h d

/-- The native étale H¹ pullback commutes with the label into actual unit
cohomology, after applying the literal ground-field semilinearity. -/
theorem unitLabel_pullback (h : j ≫ k = k' ≫ Spec.map (CommRingCat.ofHom σ))
    (d : ℕ) (x : Sheaf.H ((C X).obj (M (K := K) d)) 1) :
    unitPullback j (Sheaf.H.map (unitLabel k d) 1 x) =
      Sheaf.H.map (unitLabel k' d) 1
        (Sheaf.H.map ((C U).map (fieldRootMap σ d)) 1 (constantPullback j (M (K := K) d) x)) := by
  change Sheaf.H.map (u j) 1 (pullback j (G X) (Sheaf.H.map (unitLabel k d) 1 x)) =
    Sheaf.H.map (unitLabel k' d) 1 (Sheaf.H.map ((C U).map (fieldRootMap σ d)) 1
      (Sheaf.H.map (constantComparison j (M (K := K) d)).inv 1
        (pullback j ((C X).obj (M (K := K) d)) x)))
  rw [← pullback_coeff, ← Sheaf.H.map_comp_apply, label_transport j k k' σ h d,
    Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]

end

end ManuscriptAudit.FullEtaleConstantRootHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FullEtaleConstantRootHOne.constantPullback_coeff,
      ``ManuscriptAudit.FullEtaleConstantRootHOne.unitLabel_pullback] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
