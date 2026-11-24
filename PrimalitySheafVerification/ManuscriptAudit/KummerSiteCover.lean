import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Etale
import PrimalitySheafVerification.ManuscriptAudit.KummerEtale

/-!
# Local lifting of units in the small étale site

For any affine object in the small étale site, adjoining a \(d\)-th root
of a unit gives a singleton covering sieve and a root in the coordinate
ring of its source when \(d\) is invertible.
-/

namespace ManuscriptAudit.KummerSiteCover

open AlgebraicGeometry CategoryTheory

universe u

/-- A surjective arrow between objects of the small étale site is a
singleton covering family. -/
theorem singleton_mem_smallEtaleTopology {X : Scheme.{u}} {U V : X.Etale}
    (f : V ⟶ U) (hs : Function.Surjective f.left) :
    Sieve.ofArrows (fun _ : Unit => V) (fun _ : Unit => f) ∈ X.smallEtaleTopology U := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, hy⟩ := hs x
  exact Set.mem_iUnion.mpr ⟨(), y, hy⟩

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

abbrev rootAlgebra (d : ℕ) (a : Aˣ) :=
  AdjoinRoot (KummerEtale.kummerPolynomial d (a : A))

/-- The structure morphism of the root algebra over its affine target. -/
noncomputable def rootMap (d : ℕ) (a : Aˣ) :
    Spec (CommRingCat.of (rootAlgebra d a)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (rootAlgebra d a)))

/-- The root algebra as an object of the small étale site. -/
noncomputable def rootObject (g : Spec (CommRingCat.of A) ⟶ X) [Etale g]
    {d : ℕ} (hpos : 0 < d) (hd : IsUnit (d : A)) (a : Aˣ) : X.Etale := by
  letI : Etale (rootMap d a) :=
    (KummerEtale.kummer_spec_finite_etale_cover hpos hd a.isUnit).2.1
  exact Scheme.Etale.mk (rootMap d a ≫ g)

/-- The map from the root object to the original affine étale object. -/
noncomputable def rootArrow (g : Spec (CommRingCat.of A) ⟶ X) [Etale g]
    {d : ℕ} (hpos : 0 < d) (hd : IsUnit (d : A)) (a : Aˣ) :
    rootObject g hpos hd a ⟶ Scheme.Etale.mk g := by
  refine MorphismProperty.Over.homMk (rootMap d a) ?_
  rfl

/-- A unit on any affine étale object lifts to a \(d\)-th power on its
actual Kummer covering object. -/
theorem unit_lifts_on_affine_etale_cover (g : Spec (CommRingCat.of A) ⟶ X) [Etale g]
    {d : ℕ} (hpos : 0 < d) (hd : IsUnit (d : A)) (a : Aˣ) :
    (Sieve.ofArrows (fun _ : Unit => rootObject g hpos hd a)
        (fun _ : Unit => rootArrow g hpos hd a) ∈ X.smallEtaleTopology (Scheme.Etale.mk g)) ∧
      ∃ v : (rootAlgebra d a)ˣ, (v : rootAlgebra d a) ^ d =
        algebraMap A (rootAlgebra d a) (a : A) := by
  constructor
  · apply singleton_mem_smallEtaleTopology
    change Function.Surjective (rootMap d a)
    exact AlgebraicGeometry.surjective_iff.mp
      (KummerEtale.kummer_spec_finite_etale_cover hpos hd a.isUnit).2.2
  · obtain ⟨v, hv⟩ := KummerEtale.kummer_root_isUnit hpos a.isUnit
    refine ⟨v, ?_⟩
    rw [hv]
    exact KummerEtale.kummer_root_pow d (a : A)

end ManuscriptAudit.KummerSiteCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.KummerSiteCover.singleton_mem_smallEtaleTopology,
      ``ManuscriptAudit.KummerSiteCover.unit_lifts_on_affine_etale_cover] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
