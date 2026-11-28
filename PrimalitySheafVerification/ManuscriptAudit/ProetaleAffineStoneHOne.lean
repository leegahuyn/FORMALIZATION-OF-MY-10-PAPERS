import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineRechart
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineSingletonLift
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineStoneCech
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.SheafExplicitCechHOne
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-! The native degree-one finite-coefficient cohomology vanishes on an
actual affine weakly étale scheme over an algebraically closed field. -/

namespace ManuscriptAudit.ProetaleAffineStoneHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap)
open ProetaleAffineRechart
open ProetaleCechPullbackGeometry
open ProetaleContinuousDirectImageMaps (functions)
open SingletonCoverRefinement (Covers)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K A M : Type} [Field K] [IsAlgClosed K] [CommRing A]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [Finite M]

private abbrev J := Scheme.ProEt.topology (spectrum A)
private abbrev G := AddCommGrpCat.{1}
private abbrev C := Sheaf (J (A := A)) G
private abbrev F := functions M (spectrum A)

local instance : EnoughInjectives (C (A := A)) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := C (A := A))

variable (c : spectrum A ⟶ Spec (CommRingCat.of K)) [WeaklyEtale c]
variable {B : Type} [CommRing B] [Algebra A B] [WeaklyEtale (structureMap A B)]
  [Surjective (structureMap A B)]

private theorem specCover :
    Covers (J (A := A)) (toTerminal (structureMap A B)) := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.singleton (toTerminal (structureMap A B))).map
      (Scheme.ProEt.forget (spectrum A) ⋙ Over.forget (spectrum A)) ∈
    Scheme.proetalePrecoverage (spectrum A)
  rw [Presieve.map_singleton]
  change Presieve.singleton (structureMap A B) ∈ Scheme.propQCPrecoverage @WeaklyEtale (spectrum A)
  exact Scheme.Hom.singleton_mem_propQCPrecoverage
    (inferInstanceAs (WeaklyEtale (structureMap A B)))

include c in
set_option maxHeartbeats 2000000 in
private theorem lift_from_spec {I : C (A := A)} (i : F (A := A) (M := M) ⟶ I) [Mono i]
    (x : (cokernel i).obj.obj (op (terminal (spectrum A))))
    (y : I.obj.obj (op (coveringObject (structureMap A B))))
    (hy : (cokernel.π i).hom.app _ y =
      (cokernel i).obj.map (toTerminal (structureMap A B)).op x) :
    ∃ z : I.obj.obj (op (terminal (spectrum A))), (cokernel.π i).hom.app _ z = x := by
  let p := structureMap A B
  let f := toTerminal p
  let hP := double_isPullback p
  obtain ⟨b, hb, hbCocycle⟩ := SheafExplicitCechHOne.exists_cocycle i f (p₀ p) (p₁ p) hP
    (e₀₁ p) (e₀₂ p) (e₁₂ p) (face_first_first p) (face_second_first p)
    (face_second_second p) x y hy
  let b' : C(↥(D p), M) := b.down
  have hCocycle (z : ↥(E p)) :
      b' (d₁₂ p z) - b' (d₀₂ p z) + b' (d₀₁ p z) = 0 := by
    have h := congrArg (fun q : (F (A := A) (M := M)).obj.obj (op (triple p)) ↦
      (show C(↥(E p), M) from q.down) z) hbCocycle
    exact h
  obtain ⟨a, ha⟩ := ProetaleAffineStoneCech.exists_primitive c p b' hCocycle
  let a' : (F (A := A) (M := M)).obj.obj (op (coveringObject p)) := ⟨a⟩
  apply SheafExplicitCechHOne.exists_global_lift i f (p₀ p) (p₁ p) hP
    (specCover (A := A) (B := B)) x y hy a'
  rw [← hb]
  apply congrArg (i.hom.app (op (double p)))
  apply ULift.ext
  apply ContinuousMap.ext
  exact ha

include c in
set_option maxHeartbeats 2000000 in
/-- The actual continuous finite-coefficient sheaf has zero native H¹
on this entire affine weakly étale spectrum. -/
theorem HOne_subsingleton : Subsingleton (Sheaf.H (F (A := A) (M := M)) 1) := by
  let I := Injective.under (F (A := A) (M := M))
  let i : F (A := A) (M := M) ⟶ I := Injective.ι _
  let T := terminal (spectrum A)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale (spectrum A)
  letI : IsAffine T.left := inferInstanceAs (IsAffine (spectrum A))
  apply SheafH1Descent.H1_subsingleton_of_global_lifts i hT
  let π := cokernel.π i
  letI : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' G π).mpr inferInstance
  intro x
  obtain ⟨W, f, ha, _, hs, _, y, hy⟩ :=
    ProetaleAffineSingletonLift.exists_singleton_cover_lift (T := T) π x
  letI := ha
  let B : Type := coordinateRing A W
  letI : CommRing B := inferInstanceAs (CommRing (coordinateRing A W))
  letI : Algebra A B := coordinateAlgebra A W
  letI : WeaklyEtale (structureMap A B) := coordinateChartWeaklyEtale A W
  letI : Surjective (structureMap A B) := coordinateChartSurjective A W hs
  let q := rechart A W
  let y' := I.obj.map q.op y
  apply lift_from_spec c i x y'
  change π.hom.app _ (I.obj.map q.op y) = _
  rw [NatTrans.naturality_apply π.hom q.op y, hy, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, rechart_comp_toTerminal] <;> rfl

end
end ManuscriptAudit.ProetaleAffineStoneHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAffineStoneHOne.HOne_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
