import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.Topology.LocallyConstant.Basic

/-! Continuous maps from locally Noetherian schemes to Hausdorff spaces
are locally constant on each actual small étale chart. -/

namespace ManuscriptAudit.EtaleLocallyConstantHausdorff

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

/-- In a Noetherian space a continuous Hausdorff-valued map is locally
constant because its image is Noetherian and discrete. -/
theorem of_noetherian {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    {M : Type v} [TopologicalSpace M] [T2Space M] {f : X → M} (hf : Continuous f) :
    IsLocallyConstant f := by
  letI : NoetherianSpace (Set.range f) := NoetherianSpace.range f hf
  letI : DiscreteTopology (Set.range f) := NoetherianSpace.discrete
  let g : X → Set.range f := fun x ↦ ⟨f x, ⟨x, rfl⟩⟩
  have hg : Continuous g := hf.subtype_mk _
  exact ((IsLocallyConstant.iff_continuous g).mpr hg).comp Subtype.val

/-- An affine cover of a locally Noetherian scheme gives local
constancy of every continuous Hausdorff-valued map. -/
theorem of_locallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X]
    {M : Type v} [TopologicalSpace M] [T2Space M] {f : X → M} (hf : Continuous f) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_exists_open f).mpr
  intro x
  let i := X.affineCover.idx x
  let Y := X.affineCover.X i
  let a := X.affineCover.f i
  letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion a
  letI : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  letI : NoetherianSpace Y := noetherianSpace_of_isAffine
  obtain ⟨y, hy⟩ : x ∈ Set.range a := X.affineCover.covers x
  obtain ⟨V, hV, hyV, hconst⟩ :=
    (of_noetherian (hf.comp a.continuous)).exists_open y
  refine ⟨a '' V, a.isOpenEmbedding.isOpenMap _ hV, ⟨y, hyV, hy⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (hconst z hz).trans (congrArg f hy)

/-- Restricting to any actual small étale chart of a locally Noetherian
scheme turns a continuous Hausdorff-valued map into a locally constant one. -/
theorem of_etaleChart (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Etale)
    {M : Type v} [TopologicalSpace M] [T2Space M] {f : U.left → M} (hf : Continuous f) :
    IsLocallyConstant f := by
  letI : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  exact of_locallyNoetherian U.left hf

end ManuscriptAudit.EtaleLocallyConstantHausdorff

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleLocallyConstantHausdorff.of_noetherian,
      ``ManuscriptAudit.EtaleLocallyConstantHausdorff.of_locallyNoetherian,
      ``ManuscriptAudit.EtaleLocallyConstantHausdorff.of_etaleChart] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
