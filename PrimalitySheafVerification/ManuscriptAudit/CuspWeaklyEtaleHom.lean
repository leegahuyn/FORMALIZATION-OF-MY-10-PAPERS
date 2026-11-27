import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspEtaleHom
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineUnramified

/-! Cusp pullback is bijective on morphisms between actual affine weakly
étale schemes in every characteristic. The checked algebraic Hom comparison
only needs a flat source and a formally unramified target. -/

namespace ManuscriptAudit.CuspWeaklyEtaleHom

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

private abbrev A := CuspPunctured.CuspSubalgebra K
private abbrev base := Spec (CommRingCat.of (A K))

/-- The actual affine scheme pullback is bijective on Hom sets for weakly étale objects. -/
theorem overPullback_map_bijective (T P : CommRingCat.{u})
    (f : Spec T ⟶ base K) (g : Spec P ⟶ base K) [WeaklyEtale f] [WeaklyEtale g] :
    Function.Bijective ((Over.pullback (CuspScheme.cuspMap K)).map :
      (Over.mk f ⟶ Over.mk g) → _) := by
  obtain ⟨f', rfl⟩ := Spec.map_surjective f
  obtain ⟨g', rfl⟩ := Spec.map_surjective g
  letI : Algebra (A K) T := f'.hom.toAlgebra
  letI : Algebra (A K) P := g'.hom.toAlgebra
  have hf : Spec.map (CommRingCat.ofHom (algebraMap (A K) T)) = Spec.map f' :=
    congrArg Spec.map (CommRingCat.ofHom_hom f')
  have hg : Spec.map (CommRingCat.ofHom (algebraMap (A K) P)) = Spec.map g' :=
    congrArg Spec.map (CommRingCat.ofHom_hom g')
  letI : Module.Flat (A K) T := RingHom.flat_algebraMap_iff.mp
    ((HasRingHomProperty.Spec_iff (P := @Flat) (φ := f')).mp (inferInstanceAs (Flat (Spec.map f'))))
  letI : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap (A K) P))) :=
    hg.symm ▸ inferInstanceAs (WeaklyEtale (Spec.map g'))
  letI := WeaklyEtaleAffineUnramified.formallyUnramified (A K) P
  simpa only [hf, hg] using
    (CuspEtaleHom.overPullback_map_bijective_of_algebras K (P := P) (T := T))

end
end ManuscriptAudit.CuspWeaklyEtaleHom

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspWeaklyEtaleHom.overPullback_map_bijective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
