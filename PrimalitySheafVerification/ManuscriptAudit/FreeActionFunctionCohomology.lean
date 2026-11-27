import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.GroupAction.Defs
import PrimalitySheafVerification.ManuscriptAudit.CoinducedFunctionRepresentation

/-!
# Functions on a free right group action

A free right group action is a disjoint union of right-translation
orbits. Functions on it form a coinduced representation and hence
have no positive cohomology.
-/

namespace ManuscriptAudit.FreeActionFunctionCohomology

open CategoryTheory CategoryTheory.Limits
open CoinducedFunctionRepresentation

universe u

noncomputable section

variable (k G X M : Type u) [CommRing k] [Group G]
  [MulAction Gᵐᵒᵖ X] [AddCommGroup M] [Module k M]

private abbrev O := MulAction.orbitRel.Quotient Gᵐᵒᵖ X

/-- The representation on functions on a right action, by precomposing
with right translation. -/
def actionFunctions : Rep.{u} k G :=
  Rep.of
    { toFun := fun g ↦
        { toFun := fun f : X → M ↦ fun x ↦ f (MulOpposite.op g • x)
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      map_one' := by
        apply LinearMap.ext
        intro f
        funext x
        change f ((1 : Gᵐᵒᵖ) • x) = f x
        rw [one_smul]
      map_mul' := fun g h ↦ by
        apply LinearMap.ext
        intro f
        funext x
        change f ((MulOpposite.op h * MulOpposite.op g) • x) =
          f (MulOpposite.op h • (MulOpposite.op g • x))
        rw [mul_smul] }

private def orbitCoordinates
    (hFree : ∀ x : X, Function.Injective (fun g : G ↦ MulOpposite.op g • x)) :
    O G X × G ≃ X :=
  Equiv.ofBijective (fun p ↦ MulOpposite.op p.2 • p.1.out) (by
    have hOrbit (q : O G X) (g : G) :
        Quotient.mk (MulAction.orbitRel Gᵐᵒᵖ X) (MulOpposite.op g • q.out) = q := by
      have h : MulAction.orbitRel Gᵐᵒᵖ X (MulOpposite.op g • q.out) q.out :=
        MulAction.orbitRel_apply.mpr ⟨MulOpposite.op g, rfl⟩
      exact (Quotient.sound h).trans (Quotient.out_eq q)
    constructor
    · rintro ⟨q, g⟩ ⟨r, h⟩ hEq
      change MulOpposite.op g • q.out = MulOpposite.op h • r.out at hEq
      have hq : q = r :=
        (hOrbit q g).symm.trans
          ((congrArg (Quotient.mk (MulAction.orbitRel Gᵐᵒᵖ X)) hEq).trans (hOrbit r h))
      subst r
      exact Prod.ext rfl (hFree q.out hEq)
    · intro x
      let q : O G X := Quotient.mk (MulAction.orbitRel Gᵐᵒᵖ X) x
      have hq : MulAction.orbitRel Gᵐᵒᵖ X x q.out :=
        Quotient.exact (Quotient.out_eq q).symm
      obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hq
      exact ⟨(q, MulOpposite.unop g), hg⟩)

private def functionEquiv
    (hFree : ∀ x : X, Function.Injective (fun g : G ↦ MulOpposite.op g • x)) :
    (X → M) ≃ₗ[k] (G → O G X → M) where
  toFun f g q := f (orbitCoordinates G X hFree (q, g))
  invFun f x := f ((orbitCoordinates G X hFree).symm x).2
    ((orbitCoordinates G X hFree).symm x).1
  left_inv f := funext fun x ↦ congrArg f ((orbitCoordinates G X hFree).apply_symm_apply x)
  right_inv f := by
    funext g q
    change f ((orbitCoordinates G X hFree).symm (orbitCoordinates G X hFree (q, g))).2
      ((orbitCoordinates G X hFree).symm (orbitCoordinates G X hFree (q, g))).1 = f g q
    rw [Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Functions on a free right action identify with the actual
right-translation function representation with orbit-indexed values. -/
def actionFunctionsIso
    (hFree : ∀ x : X, Function.Injective (fun g : G ↦ MulOpposite.op g • x)) :
    actionFunctions k G X M ≅ functions k G (O G X → M) :=
  Rep.mkIso <| .mk (functionEquiv k G X M hFree) (fun t ↦ by
    apply LinearMap.ext
    intro f
    funext g q
    change f (MulOpposite.op t • (MulOpposite.op g • q.out)) =
      f ((MulOpposite.op t * MulOpposite.op g) • q.out)
    rw [mul_smul])

/-- Positive group cohomology vanishes for functions on any free right action. -/
theorem actionFunctions_H_succ_isZero
    (hFree : ∀ x : X, Function.Injective (fun g : G ↦ MulOpposite.op g • x)) (n : ℕ) :
    IsZero (groupCohomology (actionFunctions k G X M) (n + 1)) :=
  (functions_H_succ_isZero k G (O G X → M) n).of_iso <|
    (groupCohomology.functor k G (n + 1)).mapIso (actionFunctionsIso k G X M hFree)

end

end ManuscriptAudit.FreeActionFunctionCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FreeActionFunctionCohomology.actionFunctionsIso,
      ``ManuscriptAudit.FreeActionFunctionCohomology.actionFunctions_H_succ_isZero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
