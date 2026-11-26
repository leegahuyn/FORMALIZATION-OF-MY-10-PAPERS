import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange

/-!
# Global sections and small étale direct image

The canonical scheme pullback sends a terminal étale object to a
terminal object. Hence evaluating the direct image at the terminal
object gives the same sections as on the source, including for the
generic-point map.
-/

namespace ManuscriptAudit.SmallEtaleBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

universe u

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

/-- Direct image on small étale sheaves preserves degree-zero cohomology. -/
def directImageHZeroEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf.H ((directImage f AddCommGrpCat.{u}).obj F) 0 ≃+ Sheaf.H F 0 := by
  let TY := ⊤_ Y.Etale
  let TX := ⊤_ X.Etale
  let B := etaleBaseChange f
  letI : PreservesFiniteLimits B := preservesFiniteLimits f
  let hY : IsTerminal TY := terminalIsTerminal
  let hX : IsTerminal TX := terminalIsTerminal
  let e : B.obj TY ≅ TX := PreservesTerminal.iso B
  let e₀ : F.obj.obj (op (B.obj TY)) ≃+ F.obj.obj (op TX) :=
    (F.obj.mapIso e.symm.op).addCommGroupIsoToAddEquiv
  let e₁ := Sheaf.H.equiv₀ ((directImage f AddCommGrpCat.{u}).obj F) hY
  exact e₁.trans (e₀.trans (Sheaf.H.equiv₀ F hX).symm)

end

end ManuscriptAudit.SmallEtaleBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.SmallEtaleBaseChange.directImageHZeroEquiv
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
