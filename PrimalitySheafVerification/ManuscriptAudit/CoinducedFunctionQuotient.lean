import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.CoinducedFunctionRepresentation

/-!
# Quotient invariants of a right-translation function representation

Functions fixed by the normal subgroup are exactly functions on its
coset space, with the induced quotient action given by right translation.
-/

namespace ManuscriptAudit.CoinducedFunctionRepresentation

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
variable (S : Subgroup G) [S.Normal]

private abbrev fixedFunctions := (functions k G M).quotientToInvariants S

private theorem invariantOnCoset (f : (fixedFunctions k G M S).V)
    (x y : G) (h : (x : G ⧸ S) = (y : G ⧸ S)) : f.1 y = f.1 x := by
  let s : S := ⟨x⁻¹ * y, QuotientGroup.eq.mp h⟩
  have hx : x * (s : G) = y := by
    change x * (x⁻¹ * y) = y
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hs := congrFun (f.property s) x
  change f.1 (x * (s : G)) = f.1 x at hs
  rwa [hx] at hs

private def fixedFunctionsEquiv : (fixedFunctions k G M S).V ≃ₗ[k] ((G ⧸ S) → M) where
  toFun f q := f.1 q.out
  invFun a :=
    ⟨fun x ↦ a (x : G ⧸ S), fun s ↦ by
      funext x
      change a ((x * (s : G) : G) : G ⧸ S) = a (x : G ⧸ S)
      apply congrArg a
      symm
      exact QuotientGroup.eq.mpr (by
        simpa only [← mul_assoc, inv_mul_cancel, one_mul] using s.property)⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    exact (invariantOnCoset k G M S f (x : G ⧸ S).out x
      (QuotientGroup.out_eq' (x : G ⧸ S))).symm
  right_inv a := funext fun q ↦ congrArg a (QuotientGroup.out_eq' q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual quotient representation on invariants is the
right-translation function representation on the quotient group. -/
def quotientInvariantsFunctionsIso :
    (functions k G M).quotientToInvariants S ≅ functions k (G ⧸ S) M :=
  Rep.mkIso <| .mk (fixedFunctionsEquiv k G M S) (fun a ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S a
    apply LinearMap.ext
    intro f
    funext q
    change f.1 (q.out * g) = f.1 ((q * QuotientGroup.mk' S g).out)
    apply invariantOnCoset k G M S f
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq'] <;> rfl)

/-- Taking invariants and passing to the quotient group preserves positive
acyclicity of these function representations. -/
theorem quotientInvariantsFunctions_H_succ_isZero (n : ℕ) :
    IsZero (groupCohomology ((functions k G M).quotientToInvariants S) (n + 1)) :=
  (functions_H_succ_isZero k (G ⧸ S) M n).of_iso <|
    (groupCohomology.functor k (G ⧸ S) (n + 1)).mapIso
      (quotientInvariantsFunctionsIso k G M S)

end

end ManuscriptAudit.CoinducedFunctionRepresentation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoinducedFunctionRepresentation.quotientInvariantsFunctionsIso,
      ``ManuscriptAudit.CoinducedFunctionRepresentation.quotientInvariantsFunctions_H_succ_isZero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
