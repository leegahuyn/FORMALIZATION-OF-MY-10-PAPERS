import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Proetale
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleGeometricPointLift

/-! Algebraically closed geometric points lift along every actual small pro-étale covering sieve. -/

namespace ManuscriptAudit.ProetaleGeometricCoverLift

open AlgebraicGeometry CategoryTheory

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S : Scheme.{u}} (K : Type u) [Field K] [IsAlgClosed K]

set_option maxHeartbeats 500000 in
/-- A covering sieve lifts an actual geometric field point on its target through one of its arrows. -/
theorem exists_lift {U : S.ProEt} (R : Sieve U) (hR : R ∈ Scheme.ProEt.topology S U)
    (a : Spec (CommRingCat.of K) ⟶ U.left) :
    ∃ (V : S.ProEt) (f : V ⟶ U), R f ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ V.left, b ≫ f.left = a := by
  let J := Scheme.ProEt.precoverage S
  let G := Scheme.ProEt.forget S ⋙ Over.forget S
  obtain ⟨P, hP, hPR⟩ := (J.mem_toGrothendieck_iff_of_isStableUnderComposition).mp hR
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hP
  obtain ⟨E, rfl⟩ := hP
  have hG : E.presieve₀.map G ∈ Scheme.proetalePrecoverage U.left := E.mem₀
  have hbase : E.presieve₀.map G ∈ Scheme.precoverage @WeaklyEtale U.left := hG.2
  change (Presieve.ofArrows E.X E.f).map G ∈ Scheme.precoverage @WeaklyEtale U.left at hbase
  rw [Presieve.map_ofArrows] at hbase
  have h := (Scheme.ofArrows_mem_precoverage_iff @WeaklyEtale).mp hbase
  obtain ⟨i, x, hx⟩ := h.1 (a (IsLocalRing.closedPoint K))
  letI : WeaklyEtale (E.f i).left := h.2 i
  change (E.X i).left at x
  change (E.f i).left x = a (IsLocalRing.closedPoint K) at hx
  obtain ⟨b, hb, _⟩ := WeaklyEtaleGeometricPointLift.exists_lift K (E.f i).left a x hx
  exact ⟨E.X i, E.f i, hPR _ _ ⟨i⟩, b, hb⟩

end
end ManuscriptAudit.ProetaleGeometricCoverLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleGeometricCoverLift.exists_lift
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
