import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.ProetaleRestrictionLocalLift
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteQuasiCompactCover

/-! Surjective quasi-compact weakly étale restriction detects epimorphisms. -/

namespace ManuscriptAudit.ProetaleSurjectiveRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension (proetalePostcompose postcomposeCoverPreserving)
open ProetaleBaseChange (baseChange)
open ProetaleObjectRestriction (restriction)

noncomputable section
universe u v

variable {Y X : Scheme.{u}} (j : Y ⟶ X) [WeaklyEtale j] [QuasiCompact j]
variable (hj : Function.Surjective j)

private theorem pullback_surjective (U : X.ProEt) :
    Function.Surjective (pullback.fst U.hom j) := by
  intro x
  obtain ⟨y, hy⟩ := hj (U.hom x)
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.hom) (g := j) x y hy.symm
  exact ⟨z, hz⟩

private abbrev sectionArrow (U : X.ProEt) :
    (proetalePostcompose j).obj ((baseChange j).obj U) ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom j)
    (pullback.condition (f := U.hom) (g := j))

include hj in
private theorem singleton_cover (U : X.ProEt) :
    Sieve.ofArrows
      (fun _ : PUnit.{u+1} ↦ (proetalePostcompose j).obj ((baseChange j).obj U))
      (fun _ ↦ sectionArrow j U) ∈ Scheme.ProEt.topology X U := by
  apply ProetaleFiniteQuasiCompactCover.covering
  · intro _
    change QuasiCompact (pullback.fst U.hom j)
    exact MorphismProperty.pullback_fst _ _ inferInstance
  · intro x
    obtain ⟨z, hz⟩ := pullback_surjective j hj U x
    exact ⟨⟨⟩, z, hz⟩

private abbrev A := AddCommGrpCat.{v}
private abbrev C (W : Scheme.{u}) := Sheaf (Scheme.ProEt.topology W) A.{v}

include hj in
theorem locallySurjective_of_restriction
    {F G : C.{u,v} X} (α : F ⟶ G)
    [Sheaf.IsLocallySurjective ((restriction j A.{v}).map α)] :
    Sheaf.IsLocallySurjective α where
  imageSieve_mem {U} s := by
    let Z := (baseChange j).obj U
    let L := proetalePostcompose j
    let p := sectionArrow j U
    let T := Presheaf.imageSieve α.hom s
    have hp : T.pullback p ∈ Scheme.ProEt.topology X (L.obj Z) :=
      ProetaleRestrictionLocalLift.covering_on_restriction j p α s
    apply (Scheme.ProEt.topology X).transitive (singleton_cover j hj U) T
    intro W f hf
    obtain ⟨a, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ f).mp hf
    rw [Sieve.pullback_comp]
    exact (Scheme.ProEt.topology X).pullback_stable g hp

include hj in
theorem epi_of_restriction_epi {F G : C.{u,u+1} X} (α : F ⟶ G)
    [Epi ((restriction j A.{u+1}).map α)] : Epi α := by
  letI : Sheaf.IsLocallySurjective ((restriction j A.{u+1}).map α) :=
    (Sheaf.isLocallySurjective_iff_epi' A.{u+1} _).mpr inferInstance
  letI := locallySurjective_of_restriction j hj α
  exact Sheaf.epi_of_isLocallySurjective α

end
end ManuscriptAudit.ProetaleSurjectiveRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleSurjectiveRestriction.epi_of_restriction_epi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
