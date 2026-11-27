import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineAdicClosedSectionLift
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteQuasiCompactCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedKernelLocalSupport

/-! Restriction of genuine native continuous adic coefficients to a
closed subscheme is epic, using simultaneous affine residue lifts. -/

namespace ManuscriptAudit.ProetaleAdicClosedRestrictionEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleBaseChange (baseChange)
open ProetaleClosedKernelLocalSupport (K inc)
open AffineAdicClosedSectionLift (fiberMap exists_affine_lift)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev M := ℤ_[ℓ]

set_option maxHeartbeats 2800000 in
private theorem imageSieve_mem_of_spec {R : CommRingCat.{0}} (g : Spec R ⟶ X) [WeaklyEtale g]
    (s : (functionsOver (M ℓ) i).obj.obj (op (Scheme.ProEt.mk g))) :
    Presheaf.imageSieve (diagonal (M ℓ) i).hom s ∈ J (X := X) (Scheme.ProEt.mk g) := by
  let U := Scheme.ProEt.mk g
  let t : C(↥(pullback g i : Scheme.{0}), M ℓ) := s.down
  obtain ⟨B, a, ha, haSurj, f, hLift⟩ := exists_affine_lift i ℓ g t
  letI : WeaklyEtale a := ha
  let W : X.ProEt := Scheme.ProEt.mk (a ≫ g)
  let e : W ⟶ U := MorphismProperty.Over.homMk a rfl
  have hSurj := haSurj
  rw [AlgebraicGeometry.surjective_iff] at hSurj
  have hCover : Sieve.ofArrows (fun _ : Unit ↦ W) (fun _ : Unit ↦ e) ∈ J (X := X) U :=
    ProetaleFiniteQuasiCompactCover.covering (fun _ : Unit ↦ W) (fun _ : Unit ↦ e)
      (fun _ ↦ inferInstanceAs (QuasiCompact a))
      (fun x ↦ let ⟨y, hy⟩ := hSurj x; ⟨(), y, hy⟩)
  apply (J (X := X)).superset_covering _ hCover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨u⟩
  refine ⟨⟨f⟩, ?_⟩
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change f (pullback.fst (a ≫ g) i x) = t (((baseChange i).map e).left x)
  have hMap : ((baseChange i).map e).left = fiberMap i g a := by
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, fiberMap] <;> rfl
  rw [hMap]
  exact hLift x

/-- A continuous adic section on the closed fiber has an actual native local lift. -/
theorem restriction_locallySurjective :
    Presheaf.IsLocallySurjective (J (X := X)) (diagonal (M ℓ) i).hom where
  imageSieve_mem {U} s := by
    let C := U.left.affineOpenCover
    let O := C.openCover
    apply ProetaleOpenCover.covering_of_covering_on_open U O
    intro j
    rw [Presheaf.pullback_imageSieve]
    let R := C.X j
    let g : Spec R ⟶ X := C.f j ≫ U.hom
    letI : WeaklyEtale g := inferInstance
    exact imageSieve_mem_of_spec i ℓ g _

theorem restriction_epi : Epi (diagonal (M ℓ) i) := by
  letI : Sheaf.IsLocallySurjective (diagonal (M ℓ) i) := restriction_locallySurjective i ℓ
  exact Sheaf.epi_of_isLocallySurjective (diagonal (M ℓ) i)

def sequence : ShortComplex (Sheaf (J (X := X)) A) :=
  ShortComplex.mk (inc i (M ℓ)) (diagonal (M ℓ) i) (kernel.condition (diagonal (M ℓ) i))

/-- The literal native continuous adic closed restriction sequence is short exact. -/
theorem sequence_shortExact : (sequence i ℓ).ShortExact := by
  letI := restriction_epi i ℓ
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel (sequence i ℓ) (kernelIsKernel (diagonal (M ℓ) i)))
    inferInstance inferInstance

end

end ManuscriptAudit.ProetaleAdicClosedRestrictionEpi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicClosedRestrictionEpi.restriction_epi,
      ``ManuscriptAudit.ProetaleAdicClosedRestrictionEpi.sequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
