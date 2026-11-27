import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import PrimalitySheafVerification.ManuscriptAudit.AffineProetaleBaseChangeEquivalence
import PrimalitySheafVerification.ManuscriptAudit.CuspProetaleAffineEquivalence
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUniversalHomeomorphismHOne

/-! The actual affine cusp normalization in positive characteristic identifies
the native pro-étale cohomology of continuous coefficient sheaves. -/

namespace ManuscriptAudit.CuspProetaleCohomologyEquivalence

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CuspProetaleAffineEquivalence (Cusp Normalization normalizationIsEquivalence)
open ProetaleContinuousDirectImageMaps (functions diagonal)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleConstantRestriction (constant)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

private abbrev J (X : Scheme.{0}) := Scheme.ProEt.topology X
private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (J X) A
private abbrev Z (X : Scheme.{0}) :=
  (constantSheaf (J X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

set_option maxHeartbeats 1400000 in
/-- The genuine direct image along the normalization and pullback of
continuous coefficients identify every native cohomology group. -/
def continuousEquiv (M : Type) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] (n : ℕ) :
    Sheaf.H (functions M (Cusp K)) n ≃+ Sheaf.H (functions M (Normalization K)) n := by
  let N := Normalization K
  let X := Cusp K
  let f : N ⟶ X := CuspScheme.cuspMap K
  letI : IsFinite f := CuspScheme.paper2_cusp_map_finite K
  letI : UniversallyInjective f := CuspScheme.paper2_cusp_map_universally_injective K
  letI : Surjective f := CuspScheme.paper2_cusp_map_surjective K
  letI : (AffineProetaleSite.baseChange f).IsEquivalence := normalizationIsEquivalence K p
  letI : EnoughInjectives (C N) :=
    IsGrothendieckAbelian.enoughInjectives.{1} (C := C N)
  let F : C N ⥤ C X := ProetaleBaseChange.directImage f A
  letI : F.IsEquivalence := AffineProetaleBaseChangeEquivalence.directImage_isEquivalence f
  letI : F.Additive := F.additive_of_preserves_binary_products
  let S := F.obj (functions M N)
  let i : F.obj (Z N) ≅ Z X :=
    (AffineProetaleBaseChangeEquivalence.directImageConstantIso f).app
      (AddCommGrpCat.of (ULift.{1} ℤ))
  let u := AddEquiv.ofBijective (F.mapExtAddHom (Z N) (functions M N) n)
    (F.mapExt_bijective_of_preservesInjectiveObjects (Z N) (functions M N) n)
  let v : Ext (F.obj (Z N)) S n ≃+ Ext (Z X) S n :=
    { toFun := (Ext.mk₀ i.inv).precomp S (zero_add n)
      invFun := (Ext.mk₀ i.hom).precomp S (zero_add n)
      left_inv := by
        intro a
        change (Ext.mk₀ i.hom).comp ((Ext.mk₀ i.inv).comp a (zero_add n)) (zero_add n) = a
        rw [Ext.mk₀_comp_mk₀_assoc, i.hom_inv_id, Ext.mk₀_id_comp]
      right_inv := by
        intro a
        change (Ext.mk₀ i.inv).comp ((Ext.mk₀ i.hom).comp a (zero_add n)) (zero_add n) = a
        rw [Ext.mk₀_comp_mk₀_assoc, i.inv_hom_id, Ext.mk₀_id_comp]
      map_add' := fun a b ↦ map_add ((Ext.mk₀ i.inv).precomp S (zero_add n)) a b }
  letI : IsIso (diagonal M f) := ProetaleUniversalHomeomorphismHOne.diagonal_isIso f M
  let w : functions M X ≅ S := asIso (diagonal M f)
  exact (cohomologyIso (X := X) w n).trans ((u.trans v).symm)

/-- Ordinary native cohomology of the actual affine cusp and affine line with
finite cyclic coefficients agrees, including in the characteristic. -/
def cyclicEquiv (d n : ℕ) :
    Sheaf.H (constant (Cusp K) (ZMod d)) n ≃+
      Sheaf.H (constant (Normalization K) (ZMod d)) n := by
  letI : TopologicalSpace (ZMod d) := ⊥
  letI : DiscreteTopology (ZMod d) := ⟨rfl⟩
  exact (cohomologyIso (X := Cusp K) (ProetaleDiscreteConstant.constantIso (Cusp K) (ZMod d)) n).trans
    ((continuousEquiv K p (ZMod d) n).trans
      (cohomologyIso (X := Normalization K)
        (ProetaleDiscreteConstant.constantIso (Normalization K) (ZMod d)).symm n))

/-- The native Mathlib integral ℓ-adic groups of these actual affine schemes
are invariant under the normalization in positive characteristic. -/
def adicEquiv (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (Cusp K).EllAdicCohomology ℓ n ≃+ (Normalization K).EllAdicCohomology ℓ n :=
  continuousEquiv K p ℤ_[ℓ] n

end
end ManuscriptAudit.CuspProetaleCohomologyEquivalence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspProetaleCohomologyEquivalence.continuousEquiv,
      ``ManuscriptAudit.CuspProetaleCohomologyEquivalence.cyclicEquiv,
      ``ManuscriptAudit.CuspProetaleCohomologyEquivalence.adicEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
