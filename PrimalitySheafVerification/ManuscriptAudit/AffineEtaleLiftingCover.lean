import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.LocallySurjective
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCoverProduct

/-!
# Finite lifting families in the actual affine étale site

A covering sieve on the affine étale site contains a finite jointly
surjective family of its own morphisms. Applied to the image sieve of a
section, each member carries a lift.
-/

namespace ManuscriptAudit.AffineEtaleLiftingCover

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable {X : Scheme.{u}} {U : X.AffineEtale}

set_option backward.isDefEq.respectTransparency false in
/-- A covering sieve on the affine étale site contains a finite family
whose underlying scheme maps are jointly surjective. -/
theorem finite_jointly_surjective_of_covering_sieve (S : Sieve U)
    (hS : S ∈ Scheme.AffineEtale.topology X U) :
    ∃ t : Finset S.arrows.category,
      ∀ x : ((Scheme.AffineEtale.Spec X).obj U).left,
        ∃ j ∈ t, ∃ y : ((Scheme.AffineEtale.Spec X).obj j.obj.left).left,
          ((Scheme.AffineEtale.Spec X).map j.obj.hom).left y = x := by
  let E := Scheme.AffineEtale.Spec X
  let J := S.arrows.category
  rw [Scheme.AffineEtale.topology, Functor.mem_inducedTopology_iff_of_isCoverDense] at hS
  change S.functorPushforward E ∈ X.smallEtaleTopology (E.obj U) at hS
  rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows] at hS
  have hAll := (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun j : J => E.map j.obj.hom)).mp hS
  let A := U.left.unop
  let B (j : J) := j.obj.left.left.unop
  let f (j : J) : A ⟶ B j := j.obj.hom.left.unop
  letI : ∀ j : J, Algebra (A : Type u) (B j : Type u) := fun j => (f j).hom.toAlgebra
  letI : ∀ j : J, Algebra.Etale (A : Type u) (B j : Type u) := fun j => by
    have hEt : Etale (Spec.map (f j)) := by
      change Etale (E.map j.obj.hom).left
      infer_instance
    exact (RingHom.etale_algebraMap).mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hEt)
  have hJoint : ∀ x : PrimeSpectrum A, ∃ j : J, ∃ y : PrimeSpectrum (B j),
      PrimeSpectrum.comap (algebraMap A (B j)) y = x := by
    intro x
    have hx : x ∈ ⋃ j : J, Set.range (E.map j.obj.hom).left := by
      rw [hAll]
      exact Set.mem_univ x
    obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hx
    exact ⟨j, y, hy⟩
  exact AffineEtaleCoverProduct.finite_affine_etale_subcover (fun j : J => (B j : Type u)) hJoint

/-- A locally surjective morphism of abelian sheaves gives finitely many
affine étale local lifts of a section on a jointly surjective family. -/
theorem finite_jointly_surjective_lifts
    {I Q : Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}}
    (q : I ⟶ Q) [Sheaf.IsLocallySurjective q] (x : Q.obj.obj (op U)) :
    ∃ t : Finset (Presheaf.imageSieve q.hom x).arrows.category,
      (∀ j ∈ t, ∃ y : I.obj.obj (op j.obj.left),
        q.hom.app (op j.obj.left) y = Q.obj.map j.obj.hom.op x) ∧
      ∀ z : ((Scheme.AffineEtale.Spec X).obj U).left,
        ∃ j ∈ t, ∃ y : ((Scheme.AffineEtale.Spec X).obj j.obj.left).left,
          ((Scheme.AffineEtale.Spec X).map j.obj.hom).left y = z := by
  obtain ⟨t, ht⟩ := finite_jointly_surjective_of_covering_sieve (Presheaf.imageSieve q.hom x)
    (Presheaf.imageSieve_mem (Scheme.AffineEtale.topology X) q.hom (U := op U) x)
  refine ⟨t, ?_, ht⟩
  intro j _
  exact j.property

end ManuscriptAudit.AffineEtaleLiftingCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleLiftingCover.finite_jointly_surjective_of_covering_sieve,
      ``ManuscriptAudit.AffineEtaleLiftingCover.finite_jointly_surjective_lifts] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
