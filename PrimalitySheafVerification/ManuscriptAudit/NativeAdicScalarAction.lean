import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousCoefficientNaturality

/-! The native ℓ-adic cohomology groups carry the actual scalar action
induced by multiplication on the continuous coefficient sheaf. -/

namespace ManuscriptAudit.NativeAdicScalarAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleContinuousCoefficientNaturality (map)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev F := functions ℤ_[ℓ] X

def multiply (a : ℤ_[ℓ]) : ℤ_[ℓ] →+ ℤ_[ℓ] where
  toFun x := a * x
  map_zero' := mul_zero a
  map_add' := mul_add a

theorem multiply_continuous (a : ℤ_[ℓ]) : Continuous (multiply ℓ a) :=
  continuous_const.mul continuous_id

/-- Literal scalar multiplication on every continuous-coefficient section. -/
abbrev scalarMap (a : ℤ_[ℓ]) : F X ℓ ⟶ F X ℓ :=
  map (multiply ℓ a) (multiply_continuous ℓ a) X

private theorem endo_ext (f g : F X ℓ ⟶ F X ℓ)
    (h : ∀ (U : X.ProEt) (s : ULift.{1} (C(U.left, ℤ_[ℓ]))) (x : U.left),
      (show C(U.left, ℤ_[ℓ]) from (f.hom.app (op U) s).down) x =
        (show C(U.left, ℤ_[ℓ]) from (g.hom.app (op U) s).down) x) : f = g := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  exact ContinuousMap.ext (h U.unop s)

theorem scalarMap_zero : scalarMap X ℓ 0 = 0 := by
  apply endo_ext
  intro U s x
  change (0 : ℤ_[ℓ]) * s.down x = 0
  exact zero_mul _

theorem scalarMap_one : scalarMap X ℓ 1 = 𝟙 (F X ℓ) := by
  apply endo_ext
  intro U s x
  change (1 : ℤ_[ℓ]) * s.down x = s.down x
  exact one_mul _

theorem scalarMap_add (a b : ℤ_[ℓ]) : scalarMap X ℓ (a + b) = scalarMap X ℓ a + scalarMap X ℓ b := by
  apply endo_ext
  intro U s x
  change (a + b) * s.down x = a * s.down x + b * s.down x
  exact add_mul _ _ _

theorem scalarMap_mul (a b : ℤ_[ℓ]) :
    scalarMap X ℓ (a * b) = scalarMap X ℓ b ≫ scalarMap X ℓ a := by
  apply endo_ext
  intro U s x
  change (a * b) * s.down x = a * (b * s.down x)
  exact mul_assoc _ _ _

/-- The module structure on Mathlib's actual native integral adic cohomology. -/
def adicModule (n : ℕ) : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n) where
  smul a := Sheaf.H.map (scalarMap X ℓ a) n
  one_smul x := by
    change Sheaf.H.map (scalarMap X ℓ 1) n x = x
    rw [scalarMap_one, Sheaf.H.map_id_apply]
  mul_smul a b x := by
    change Sheaf.H.map (scalarMap X ℓ (a * b)) n x =
      Sheaf.H.map (scalarMap X ℓ a) n (Sheaf.H.map (scalarMap X ℓ b) n x)
    rw [scalarMap_mul, Sheaf.H.map_comp_apply]
  smul_zero a := map_zero (Sheaf.H.map (scalarMap X ℓ a) n)
  smul_add a := map_add (Sheaf.H.map (scalarMap X ℓ a) n)
  add_smul a b x := by
    change Sheaf.H.map (scalarMap X ℓ (a + b)) n x =
      Sheaf.H.map (scalarMap X ℓ a) n x + Sheaf.H.map (scalarMap X ℓ b) n x
    rw [scalarMap_add, Sheaf.H.map_add_apply]
  zero_smul x := by
    change Sheaf.H.map (scalarMap X ℓ 0) n x = 0
    rw [scalarMap_zero]
    simp [Sheaf.H.map_apply]

end
end ManuscriptAudit.NativeAdicScalarAction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAdicScalarAction.adicModule
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
