import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.ProetaleRestrictionLocalLift

/-! Epimorphism of a native pro-étale sheaf map is local for an actual
open cover of the base scheme. -/

namespace ManuscriptAudit.ProetaleOpenRestrictionEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension (proetalePostcompose)
open ProetaleBaseChange (baseChange)
open ProetaleObjectRestriction (restriction)

noncomputable section
universe u

variable {X : Scheme.{u}} (C : X.OpenCover)
private abbrev A := AddCommGrpCat.{u+1}
private abbrev H := Sheaf (Scheme.ProEt.topology X) A.{u}

private abbrev chart (U : X.ProEt) (i : C.I₀) : X.ProEt :=
  (proetalePostcompose (C.f i)).obj ((baseChange (C.f i)).obj U)

private abbrev arrow (U : X.ProEt) (i : C.I₀) : chart C U i ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom (C.f i))
    (pullback.condition (f := U.hom) (g := C.f i))

private theorem charts_cover (U : X.ProEt) :
    Sieve.ofArrows (chart C U) (arrow C U) ∈ Scheme.ProEt.topology X U := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows (chart C U) (arrow C U)).map
    (Scheme.ProEt.forget X ⋙ Over.forget X) ∈ Scheme.proetalePrecoverage U.left
  rw [Presieve.map_ofArrows]
  apply Scheme.etalePrecoverage_le_proetalePrecoverage _
  change Presieve.ofArrows _ _ ∈ Scheme.precoverage @Etale U.left
  refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨?_, fun i ↦ ?_⟩
  · intro x
    let i := C.idx (U.hom x)
    obtain ⟨y, hy⟩ := C.covers (U.hom x)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := U.hom) (g := C.f i) x y hy.symm
    exact ⟨i, z, hz⟩
  · change Etale (pullback.fst U.hom (C.f i))
    infer_instance

/-- Epi on each genuine open restriction implies epi on the actual site. -/
theorem epi_of_openCover {F G : H.{u}} (α : F ⟶ G)
    (h : ∀ i, Epi ((restriction (C.f i) A.{u}).map α)) : Epi α := by
  have hl : Sheaf.IsLocallySurjective α := by
    constructor
    intro U s
    let R := Presheaf.imageSieve α.hom s
    apply (Scheme.ProEt.topology X).transitive (charts_cover C U) R
    intro W g hg
    obtain ⟨i, t, rfl⟩ := (Sieve.mem_ofArrows_iff (chart C U) (arrow C U) g).mp hg
    rw [Sieve.pullback_comp]
    apply (Scheme.ProEt.topology X).pullback_stable t
    letI : Sheaf.IsLocallySurjective ((restriction (C.f i) A.{u}).map α) :=
      (Sheaf.isLocallySurjective_iff_epi' A.{u} _).mpr (h i)
    exact ProetaleRestrictionLocalLift.covering_on_restriction (C.f i) (arrow C U i) α s
  letI := hl
  exact Sheaf.epi_of_isLocallySurjective α

end
end ManuscriptAudit.ProetaleOpenRestrictionEpi

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleOpenRestrictionEpi.epi_of_openCover
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
