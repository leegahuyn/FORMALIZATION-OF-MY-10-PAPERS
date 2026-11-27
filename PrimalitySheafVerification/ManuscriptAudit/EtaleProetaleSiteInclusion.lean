import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! The actual inclusion of the small étale site into the small pro-étale site. -/

namespace ManuscriptAudit.EtaleProetaleSiteInclusion

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

/-- Every étale object can be viewed as a weakly étale object over the same scheme. -/
def inclusion : X.Etale ⥤ X.ProEt :=
  MorphismProperty.Over.changeProp X (fun _ _ f hf ↦ by
    letI : Etale f := hf
    infer_instance) le_rfl

instance inclusion_preservesFiniteLimits : PreservesFiniteLimits (inclusion X) := by
  letI : PreservesFiniteLimits (inclusion X ⋙ Scheme.ProEt.forget X) := by
    change PreservesFiniteLimits (Scheme.Etale.forget X)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (inclusion X) (Scheme.ProEt.forget X)

instance inclusion_flat : RepresentablyFlat (inclusion X) :=
  flat_of_preservesFiniteLimits _

/-- The native inclusion carries the actual small étale covering sieves to pro-étale coverings. -/
theorem inclusion_coverPreserving :
    CoverPreserving X.smallEtaleTopology (Scheme.ProEt.topology X) (inclusion X) := by
  constructor
  intro U R hR
  obtain ⟨V, hV, hProp, hSub⟩ :=
    (Scheme.mem_smallGrothendieckTopology (P := @Etale) U R).mp hR
  letI := hV
  let Q := V.toPresieveOverProp hProp
  have hQ : (Q.map (inclusion X)) ∈ Scheme.ProEt.precoverage X ((inclusion X).obj U) := by
    change (Q.map (inclusion X)).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage U.left
    change ((V.toPresieveOverProp hProp).map (inclusion X)).map
      (Scheme.ProEt.forget X ⋙ Over.forget X) ∈ Scheme.proetalePrecoverage U.left
    rw [Scheme.Cover.toPresieveOverProp, Presieve.map_ofArrows, Presieve.map_ofArrows]
    exact Scheme.etalePrecoverage_le_proetalePrecoverage _ V.mem₀
  have hm := Precoverage.generate_mem_toGrothendieck hQ
  refine (Scheme.ProEt.topology X).superset_covering ?_ hm
  apply Sieve.generate_le_iff.mpr
  rintro _ _ ⟨hf⟩
  exact Presieve.image_mem_functorPushforward _ _ (hSub _ _ hf)

/-- Small étale restriction of pro-étale sheaves is induced by a continuous functor of sites. -/
instance inclusion_continuous :
    (inclusion X).IsContinuous X.smallEtaleTopology (Scheme.ProEt.topology X) :=
  (Functor.isContinuous_iff_coverPreserving (F := inclusion X)
    (J := X.smallEtaleTopology) (K := Scheme.ProEt.topology X)).mpr (inclusion_coverPreserving X)

end ManuscriptAudit.EtaleProetaleSiteInclusion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleSiteInclusion.inclusion_preservesFiniteLimits,
      ``ManuscriptAudit.EtaleProetaleSiteInclusion.inclusion_coverPreserving,
      ``ManuscriptAudit.EtaleProetaleSiteInclusion.inclusion_continuous] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
