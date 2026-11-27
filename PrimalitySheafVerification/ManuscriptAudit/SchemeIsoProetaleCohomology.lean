import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleSheaves
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! Isomorphic schemes have additively isomorphic native pro-étale
continuous-coefficient groups, in every cohomological degree. -/

namespace ManuscriptAudit.SchemeIsoProetaleCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open SchemeIsoProetaleSheaves (sheafEquivalence integersIso functionsIso)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{0}} (e : X ≅ Y)

private abbrev J (T : Scheme.{0}) := Scheme.ProEt.topology T
private abbrev A := AddCommGrpCat.{1}
private abbrev C (T : Scheme.{0}) := Sheaf (J T) A
private abbrev Z (T : Scheme.{0}) :=
  (constantSheaf (J T) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

/-- A scheme isomorphism transports any actual native coefficient sheaf. -/
def sheafCohomologyEquiv (T : C X) (n : ℕ) :
    Sheaf.H T n ≃+ Sheaf.H ((sheafEquivalence e).functor.obj T) n := by
  letI : EnoughInjectives (C X) :=
    IsGrothendieckAbelian.enoughInjectives.{1} (C := C X)
  let F : C X ⥤ C Y := (sheafEquivalence e).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  let S := F.obj T
  let i := integersIso e
  let u := AddEquiv.ofBijective (F.mapExtAddHom (Z X) T n)
    (F.mapExt_bijective_of_preservesInjectiveObjects (Z X) T n)
  let v : Ext (F.obj (Z X)) S n ≃+ Ext (Z Y) S n :=
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
  exact u.trans v

theorem sheafCohomologyEquiv_naturality {T T' : C X} (f : T ⟶ T') (n : ℕ) (x : Sheaf.H T n) :
    sheafCohomologyEquiv e T' n (Sheaf.H.map f n x) =
      Sheaf.H.map ((sheafEquivalence e).functor.map f) n (sheafCohomologyEquiv e T n x) := by
  let F := (sheafEquivalence e).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  let i := integersIso e
  change (Ext.mk₀ i.inv).comp ((x.comp (Ext.mk₀ f) (add_zero n)).mapExactFunctor F) (zero_add n) =
    ((Ext.mk₀ i.inv).comp (x.mapExactFunctor F) (zero_add n)).comp (Ext.mk₀ (F.map f)) (add_zero n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The actual cohomology with continuous coefficients is invariant under scheme isomorphisms. -/
def continuousCohomologyEquiv (M : Type) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] (n : ℕ) :
    Sheaf.H (functions M X) n ≃+ Sheaf.H (functions M Y) n :=
  (sheafCohomologyEquiv e (functions M X) n).trans
    (cohomologyIso (X := Y) (functionsIso e M) n)

/-- Mathlib's literal integral pro-étale cohomology is transported by an actual scheme isomorphism. -/
def adicCohomologyEquiv (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    X.EllAdicCohomology ℓ n ≃+ Y.EllAdicCohomology ℓ n :=
  continuousCohomologyEquiv e ℤ_[ℓ] n

end
end ManuscriptAudit.SchemeIsoProetaleCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SchemeIsoProetaleCohomology.sheafCohomologyEquiv_naturality,
      ``ManuscriptAudit.SchemeIsoProetaleCohomology.continuousCohomologyEquiv,
      ``ManuscriptAudit.SchemeIsoProetaleCohomology.adicCohomologyEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
