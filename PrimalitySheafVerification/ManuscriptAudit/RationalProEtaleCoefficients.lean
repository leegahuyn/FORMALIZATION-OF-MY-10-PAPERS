import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Rational 2-adic coefficients on the pro-étale site

Use the sheaf of continuous functions with values in the topological
field of 2-adic numbers. The restriction to the small pro-étale site
is formed in the same manner as Mathlib's integral ell-adic sheaf.
-/

namespace ManuscriptAudit.RationalProEtaleCoefficients

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The rational 2-adic coefficient sheaf on the actual small pro-étale site. -/
def rationalTwoAdicSheaf (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u} :=
  ((Scheme.ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous
    _ _ Scheme.proetaleTopology).obj
      ⟨continuousMapPresheafAb (ℚ_[2]), .of_le Scheme.proetaleTopology_le_fpqcTopology <|
        isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

/-- On every nonempty object the constant functions zero and one give distinct sections. -/
theorem sections_not_subsingleton {X : Scheme.{u}} (U : X.ProEt) (x : U.left) :
    ¬ Subsingleton ((rationalTwoAdicSheaf X).obj.obj (op U)) := by
  change ¬ Subsingleton C(U.left, ℚ_[2])
  intro h
  let f : C(U.left, ℚ_[2]) := ContinuousMap.const _ 0
  let g : C(U.left, ℚ_[2]) := ContinuousMap.const _ 1
  have he : f = g := h.elim f g
  have hx : (0 : ℚ_[2]) = 1 := congrArg (fun k : C(U.left, ℚ_[2]) => k x) he
  exact zero_ne_one hx

/-- There is only the zero section on the empty object of the site. -/
theorem sections_subsingleton_of_isEmpty {X : Scheme.{u}} (U : X.ProEt) [IsEmpty U.left] :
    Subsingleton ((rationalTwoAdicSheaf X).obj.obj (op U)) := by
  change Subsingleton C(U.left, ℚ_[2])
  constructor
  intro f g
  exact ContinuousMap.ext (fun x => isEmptyElim x)

end

end ManuscriptAudit.RationalProEtaleCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.RationalProEtaleCoefficients.rationalTwoAdicSheaf,
      ``ManuscriptAudit.RationalProEtaleCoefficients.sections_not_subsingleton,
      ``ManuscriptAudit.RationalProEtaleCoefficients.sections_subsingleton_of_isEmpty] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
