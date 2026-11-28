import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineStoneGlobalLifts
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenCover

/-! The actual closed direct image of a cokernel presentation of the
adic coefficient retains local lifts on all native affine charts. -/

namespace ManuscriptAudit.ProetaleAdicClosedImageCokernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)
open ProetaleContinuousDirectImageMaps (functions)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
variable (i : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion i]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev Z := Spec (CommRingCat.of K)
private abbrev F := functions ℤ_[ℓ] (Z (K := K))
private abbrev G := directImage i A

variable {I : Sheaf (Scheme.ProEt.topology (Z (K := K))) A}
variable (m : F (K := K) ℓ ⟶ I) [Mono m]

set_option maxHeartbeats 1600000 in
private theorem affine_sections_surjective (U : X.ProEt) [hU : IsAffine U.left] :
    Function.Surjective (((G i).map (cokernel.π m)).hom.app (op U)) := by
  let T := (baseChange i).obj U
  letI : IsAffineHom i := inferInstance
  letI : IsAffine ((𝟭 Scheme).obj U.left) := hU
  letI : IsAffine T.left :=
    show IsAffine (pullback U.hom i : Scheme.{0}) from
      isAffine_of_isAffineHom (pullback.fst U.hom i)
  intro x
  exact ProetaleAffineStoneGlobalLifts.every_affine_lift ℓ m T x

set_option maxHeartbeats 2000000 in
/-- The direct-image cokernel projection is epic for actual compact
adic coefficients along the closed algebraically closed point. -/
theorem map_cokernel_epi : Epi ((G i).map (cokernel.π m)) := by
  let q := (G i).map (cokernel.π m)
  letI : Sheaf.IsLocallySurjective q := by
    constructor
    intro U x
    let C := U.left.affineOpenCover
    let O := C.openCover
    apply ProetaleOpenCover.covering_of_covering_on_open U O
    intro k
    rw [Presheaf.pullback_imageSieve]
    let V := ProetaleOpenCover.coverObject U O k
    let e := ProetaleOpenCover.coverArrow U O k
    letI : IsAffine V.left := inferInstanceAs (IsAffine (Spec (C.X k)))
    let z := ((G i).obj (cokernel m)).obj.map e.op x
    obtain ⟨y, hy⟩ := affine_sections_surjective i ℓ m V z
    change Presheaf.imageSieve q.hom z ∈ J (X := X) V
    rw [← hy, Presheaf.imageSieve_app]
    exact (J (X := X)).top_mem V
  exact Sheaf.epi_of_isLocallySurjective q

end
end ManuscriptAudit.ProetaleAdicClosedImageCokernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicClosedImageCokernel.map_cokernel_epi
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
