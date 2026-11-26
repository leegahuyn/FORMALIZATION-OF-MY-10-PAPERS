import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.Option
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationCoordinates

/-! Rational points on the affine nodal chart and its node complement. -/

namespace ManuscriptAudit.NodalAffinePointCounts

open NodalCoordinates

variable (K : Type*) [Field K]

abbrev affinePoints := {xy : K × K // xy.2 ^ 2 = xy.1 ^ 2 * (xy.1 + 1)}
abbrev smoothAffine := {q : affinePoints K // q.val.1 ≠ 0}
abbrev twoRemoved := {t : K // t ≠ 1 ∧ t ≠ -1}

private theorem parameter_nonzero {t : K} (ht : t ≠ 1 ∧ t ≠ -1) : t ^ 2 - 1 ≠ 0 := by
  intro e
  have h := (nodal_affine_preimages_of_node t).mp ⟨e, by simp [e]⟩
  exact h.elim ht.1 ht.2

/-- The affine smooth points are the normalization line minus its two node branches. -/
def affinePunctureEquiv : twoRemoved K ≃ smoothAffine K where
  toFun t := ⟨⟨(t.val ^ 2 - 1, t.val * (t.val ^ 2 - 1)), by
    simpa using nodal_parameter_satisfies_projective_equation t.val (1 : K)⟩,
    parameter_nonzero K t.property⟩
  invFun q := by
    refine ⟨q.val.val.2 / q.val.val.1, ?_⟩
    have he := (nodal_affine_inverse_off_node q.property q.val.property).1
    constructor <;> intro h <;> rw [h] at he <;> simp at he <;>
      exact q.property he.symm
  left_inv t := by
    apply Subtype.ext
    exact mul_div_cancel_right₀ _ (parameter_nonzero K t.property)
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨hx, hy⟩ := nodal_affine_inverse_off_node q.property q.val.property
    exact Prod.ext hx hy

def node : affinePoints K := ⟨(0, 0), by simp⟩

private theorem affine_x_zero_iff (q : affinePoints K) : q.val.1 = 0 ↔ q = node K := by
  constructor
  · intro hx
    have hy2 : q.val.2 ^ 2 = 0 := by simpa [hx] using q.property
    have hy : q.val.2 = 0 := (mul_eq_zero.mp (by simpa [pow_two] using hy2)).elim id id
    exact Subtype.ext (Prod.ext hx hy)
  · rintro rfl
    rfl

/-- Adding the affine node accounts for all points of the affine equation. -/
noncomputable def affineEquiv : Option (smoothAffine K) ≃ affinePoints K := by
  classical
  let e : smoothAffine K ≃ {q : affinePoints K // q ≠ node K} :=
    Equiv.subtypeEquivProp (funext fun q => propext (not_congr (affine_x_zero_iff K q)))
  exact (Equiv.optionCongr e).trans (Equiv.optionSubtypeNe (node K))

theorem twoRemoved_card [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (twoRemoved K) + 2 = Nat.card K := by
  classical
  have hn : (-1 : K) ≠ 1 := by
    intro he
    apply h2
    linear_combination -he
  let c : {t : K // t ≠ 1} := ⟨-1, hn⟩
  let e : twoRemoved K ≃ {t : {t : K // t ≠ 1} // t ≠ c} :=
    { toFun := fun t => ⟨⟨t.val, t.property.1⟩,
        fun he => t.property.2 (congrArg Subtype.val he)⟩
      invFun := fun t => ⟨t.val.val, t.val.property,
        fun he => t.property (Subtype.ext he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e' : Option (Option (twoRemoved K)) ≃ K :=
    (Equiv.optionCongr ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe c))).trans
      (Equiv.optionSubtypeNe (1 : K))
  letI : Fintype (twoRemoved K) := Fintype.ofFinite _
  letI : Fintype K := Fintype.ofFinite _
  have hc := Fintype.card_congr e'
  simpa only [Fintype.card_option, Nat.card_eq_fintype_card, Nat.add_assoc] using hc

theorem affine_point_counts [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (smoothAffine K) + 2 = Nat.card K ∧
    Nat.card (affinePoints K) + 1 = Nat.card K := by
  classical
  letI : Fintype (affinePoints K) := Fintype.ofFinite _
  letI : Fintype (smoothAffine K) := Fintype.ofFinite _
  have hA := Fintype.card_congr (affineEquiv K)
  rw [Fintype.card_option] at hA
  have hS : Nat.card (smoothAffine K) + 2 = Nat.card K := by
    rw [← Nat.card_congr (affinePunctureEquiv K)]
    exact twoRemoved_card K h2
  have hA' : Nat.card (smoothAffine K) + 1 = Nat.card (affinePoints K) := by
    simpa only [Nat.card_eq_fintype_card] using hA
  exact ⟨hS, by omega⟩

end ManuscriptAudit.NodalAffinePointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalAffinePointCounts.affinePunctureEquiv,
      ``ManuscriptAudit.NodalAffinePointCounts.twoRemoved_card,
      ``ManuscriptAudit.NodalAffinePointCounts.affine_point_counts] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
