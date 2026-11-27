import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Relative smooth loci are respected by actual scheme isomorphisms over a base. -/

namespace ManuscriptAudit.SmoothLocusUnderIso

open AlgebraicGeometry CategoryTheory

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y S : Scheme.{u}} (e : X ≅ Y) (f : X ⟶ S) (g : Y ⟶ S)
  [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]

private theorem range_eq (h : e.hom ≫ g = f) :
    Set.range (f.smoothLocus.ι ≫ e.hom) = Set.range g.smoothLocus.ι := by
  have hS : e.hom ⁻¹ᵁ g.smoothLocus = f.smoothLocus := by
    rw [e.hom.preimage_smoothLocus_eq g, h]
  rw [Scheme.Opens.range_ι]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change e.hom x.val ∈ g.smoothLocus
    apply (e.hom.mem_preimage).mp
    rw [hS]
    exact x.property
  · intro hy
    obtain ⟨x, hx⟩ := e.hom.homeomorph.surjective y
    change e.hom x = y at hx
    have hmem : x ∈ f.smoothLocus := by
      rw [← hS]
      apply (e.hom.mem_preimage).mpr
      rw [hx]
      exact hy
    exact ⟨⟨x, hmem⟩, hx⟩

/-- The actual isomorphism of relative smooth subschemes induced by the base-preserving iso. -/
def iso (h : e.hom ≫ g = f) :
    f.smoothLocus.toScheme ≅ g.smoothLocus.toScheme :=
  IsOpenImmersion.isoOfRangeEq (f.smoothLocus.ι ≫ e.hom) g.smoothLocus.ι
    (range_eq e f g h)

end
end ManuscriptAudit.SmoothLocusUnderIso

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SmoothLocusUnderIso.iso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
