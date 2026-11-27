import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.CoinducedFunctionRepresentation

/-!
# Restriction of a right-translation function representation

Choosing a representative for each coset identifies restriction to a
subgroup with right-translation functions on that subgroup, one copy
for each coset.
-/

namespace ManuscriptAudit.CoinducedFunctionRepresentation

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]

private def cosetCoordinates (S : Subgroup G) : (G ⧸ S) × S ≃ G where
  toFun p := p.1.out * (p.2 : G)
  invFun x := ((x : G ⧸ S), ⟨(x : G ⧸ S).out⁻¹ * x,
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : G ⧸ S))⟩)
  left_inv p := by
    obtain ⟨q, s⟩ := p
    have hq' : (q.out : G ⧸ S) = ((q.out * (s : G) : G) : G ⧸ S) :=
      QuotientGroup.eq.mpr (by simpa only [← mul_assoc, inv_mul_cancel, one_mul]
        using s.property)
    have hq : ((q.out * (s : G) : G) : G ⧸ S) = q :=
      hq'.symm.trans (QuotientGroup.out_eq' q)
    apply Prod.ext
    · exact hq
    · apply Subtype.ext
      change ((q.out * (s : G) : G) : G ⧸ S).out⁻¹ * (q.out * (s : G)) = (s : G)
      rw [hq, ← mul_assoc, inv_mul_cancel, one_mul]
  right_inv x := by
    change (x : G ⧸ S).out * ((x : G ⧸ S).out⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel, one_mul]

private def restrictionEquiv (S : Subgroup G) :
    (G → M) ≃ₗ[k] (S → (G ⧸ S) → M) where
  toFun f s q := f (cosetCoordinates G S (q, s))
  invFun f x := f ((cosetCoordinates G S).symm x).2 ((cosetCoordinates G S).symm x).1
  left_inv f := funext fun x ↦ congrArg f ((cosetCoordinates G S).apply_symm_apply x)
  right_inv f := by
    funext s q
    change f ((cosetCoordinates G S).symm (cosetCoordinates G S (q, s))).2
      ((cosetCoordinates G S).symm (cosetCoordinates G S (q, s))).1 = f s q
    rw [Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The native restricted representation is coinduced from the trivial
subgroup of the restricting subgroup. -/
def restrictionFunctionsIso (S : Subgroup G) :
    Rep.res S.subtype (functions k G M) ≅ functions k S ((G ⧸ S) → M) :=
  Rep.mkIso <| .mk (restrictionEquiv k G M S) (fun t ↦ by
    apply LinearMap.ext
    intro f
    funext s q
    change f ((q.out * (s : G)) * (t : G)) = f (q.out * (((s * t : S) : G)))
    rw [Subgroup.coe_mul, mul_assoc])

/-- Restriction to any subgroup preserves positive acyclicity of these
function representations. -/
theorem restrictionFunctions_H_succ_isZero (S : Subgroup G) (n : ℕ) :
    IsZero (groupCohomology (Rep.res S.subtype (functions k G M)) (n + 1)) :=
  (functions_H_succ_isZero k S ((G ⧸ S) → M) n).of_iso
    ((groupCohomology.functor k S (n + 1)).mapIso (restrictionFunctionsIso k G M S))

end

end ManuscriptAudit.CoinducedFunctionRepresentation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoinducedFunctionRepresentation.restrictionFunctionsIso,
      ``ManuscriptAudit.CoinducedFunctionRepresentation.restrictionFunctions_H_succ_isZero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
