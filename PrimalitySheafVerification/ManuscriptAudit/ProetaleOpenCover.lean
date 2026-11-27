import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! Ordinary open covers give actual covering sieves of the native
small pro-étale site. -/

namespace ManuscriptAudit.ProetaleOpenCover

open AlgebraicGeometry CategoryTheory

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (U : X.ProEt) (C : U.left.OpenCover)

/-- View the source of an open covering arrow in the same native site. -/
abbrev coverObject (i : C.I₀) : X.ProEt := Scheme.ProEt.mk (C.f i ≫ U.hom)

abbrev coverArrow (i : C.I₀) : coverObject U C i ⟶ U :=
  MorphismProperty.Over.homMk (C.f i) rfl

theorem covering :
    Sieve.ofArrows (coverObject U C) (coverArrow U C) ∈ Scheme.ProEt.topology X U := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows (coverObject U C) (coverArrow U C)).map
    (Scheme.ProEt.forget X ⋙ Over.forget X) ∈ Scheme.proetalePrecoverage U.left
  rw [Presieve.map_ofArrows]
  apply Scheme.etalePrecoverage_le_proetalePrecoverage _
  change Presieve.ofArrows C.X C.f ∈ Scheme.precoverage @Etale U.left
  exact (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
    ⟨fun x ↦ ⟨C.idx x, C.covers x⟩, fun _ ↦ inferInstance⟩

/-- It is enough to check a sieve after pulling back to the usual open cover. -/
theorem covering_of_covering_on_open (R : Sieve U)
    (h : ∀ i, R.pullback (coverArrow U C i) ∈
      Scheme.ProEt.topology X (coverObject U C i)) :
    R ∈ Scheme.ProEt.topology X U := by
  apply (Scheme.ProEt.topology X).transitive (covering U C)
  rintro V a ⟨_, b, _, ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  exact (Scheme.ProEt.topology X).pullback_stable b (h i)

end
end ManuscriptAudit.ProetaleOpenCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenCover.covering,
      ``ManuscriptAudit.ProetaleOpenCover.covering_of_covering_on_open] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
