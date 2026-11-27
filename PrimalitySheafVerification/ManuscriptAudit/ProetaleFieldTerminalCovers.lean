import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Proetale
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAlgebraicallyClosed

/-! The actual terminal object of the pro-étale site of an algebraically
closed field has only the maximal covering sieve. -/

namespace ManuscriptAudit.ProetaleFieldTerminalCovers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

abbrev base := Spec (CommRingCat.of K)

/-- The actual pro-étale identity object of the field. -/
def terminalObject : (base K).ProEt :=
  Scheme.ProEt.mk (𝟙 (base K))

theorem terminalObject_isTerminal : IsTerminal (terminalObject K) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale (base K)

variable [IsAlgClosed K]

/-- Every covering sieve of the actual pro-étale terminal field object
contains the identity. -/
theorem covering_eq_top (R : Sieve (terminalObject K))
    (hR : R ∈ Scheme.ProEt.topology (base K) (terminalObject K)) : R = ⊤ := by
  let S := base K
  let T := terminalObject K
  let J := Scheme.ProEt.precoverage S
  let G := Scheme.ProEt.forget S ⋙ Over.forget S
  obtain ⟨P, hP, hPR⟩ := (J.mem_toGrothendieck_iff_of_isStableUnderComposition).mp hR
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hP
  obtain ⟨E, rfl⟩ := hP
  have hG : E.presieve₀.map G ∈ Scheme.proetalePrecoverage S := E.mem₀
  have hbase : E.presieve₀.map G ∈ Scheme.precoverage @WeaklyEtale S := hG.2
  change (Presieve.ofArrows E.X E.f).map G ∈ Scheme.precoverage @WeaklyEtale S at hbase
  rw [Presieve.map_ofArrows] at hbase
  obtain ⟨i, x, _⟩ := ((Scheme.ofArrows_mem_precoverage_iff @WeaklyEtale).mp hbase).1
    (IsLocalRing.closedPoint K)
  change (E.X i).left at x
  obtain ⟨s, hs, _⟩ :=
    WeaklyEtaleAlgebraicallyClosed.rationalSectionThrough K (E.X i).hom x
  let a : T ⟶ E.X i := MorphismProperty.Over.homMk s hs
  have h : a ≫ E.f i = 𝟙 T := (terminalObject_isTerminal K).hom_ext _ _
  apply (Sieve.id_mem_iff_eq_top R).mp
  have ha := R.downward_closed (hPR _ (E.f i) ⟨i⟩) a
  rwa [h] at ha

end
end ManuscriptAudit.ProetaleFieldTerminalCovers

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleFieldTerminalCovers.covering_eq_top
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
