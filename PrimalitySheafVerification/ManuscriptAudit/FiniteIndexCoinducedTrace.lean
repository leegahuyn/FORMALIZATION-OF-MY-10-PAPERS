import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Coinduced

/-!
# The finite-index trace from a coinduced representation

The coinduced functions for a restricted representation are equivariant
under multiplication by the subgroup on the left. Applying the inverse
action to their values gives a function on the right cosets. Summing this
normalized function defines the trace back to the original representation.
-/

namespace ManuscriptAudit.FiniteIndexCoinducedTrace

open CategoryTheory
open scoped BigOperators

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]
variable (S : Subgroup G) (A : Rep.{u} k G)

private abbrev RightCosets := Quotient (QuotientGroup.rightRel S)

private abbrev CoindRes := Rep.coind S.subtype (Rep.res S.subtype A)

private def cosetRightMul (g : G) : RightCosets S ≃ RightCosets S where
  toFun := Quotient.map' (· * g) (fun x y h ↦ by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_inv_rev, mul_assoc] using h)
  invFun := Quotient.map' (· * g⁻¹) (fun x y h ↦ by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_inv_rev, mul_assoc] using h)
  left_inv q := Quotient.ind' (fun x ↦ by
    change Quotient.mk'' ((x * g) * g⁻¹) = Quotient.mk'' x
    simp [mul_assoc]) q
  right_inv q := Quotient.ind' (fun x ↦ by
    change Quotient.mk'' ((x * g⁻¹) * g) = Quotient.mk'' x
    simp [mul_assoc]) q

private def normalizedValue (f : CoindRes S A) : RightCosets S → A.V := by
  refine Quotient.lift (fun x : G ↦ A.ρ x⁻¹ (f.1 x)) ?_
  intro x y h
  change QuotientGroup.rightRel S x y at h
  rw [QuotientGroup.rightRel_apply] at h
  let s : S := ⟨y * x⁻¹, h⟩
  have hy : (s : G) * x = y := by simp [s, mul_assoc]
  have hf : f.1 ((s : G) * x) = A.ρ s (f.1 x) := f.2 s x
  calc
    A.ρ x⁻¹ (f.1 x) = A.ρ ((s : G) * x)⁻¹ (A.ρ s (f.1 x)) := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp [mul_inv_rev, mul_assoc]
    _ = A.ρ y⁻¹ (f.1 y) := by rw [← hf, hy]

private theorem normalizedValue_add (f h : CoindRes S A) (q : RightCosets S) :
    normalizedValue S A (f + h) q = normalizedValue S A f q + normalizedValue S A h q := by
  refine Quotient.ind' (fun x ↦ ?_) q
  change A.ρ x⁻¹ (f.1 x + h.1 x) = _
  exact map_add (A.ρ x⁻¹) _ _

private theorem normalizedValue_smul (r : k) (f : CoindRes S A) (q : RightCosets S) :
    normalizedValue S A (r • f) q = r • normalizedValue S A f q := by
  refine Quotient.ind' (fun x ↦ ?_) q
  change A.ρ x⁻¹ (r • f.1 x) = _
  exact map_smul (A.ρ x⁻¹) _ _

private theorem normalizedValue_action (g : G) (f : CoindRes S A) (q : RightCosets S) :
    normalizedValue S A ((CoindRes S A).ρ g f) q =
      A.ρ g (normalizedValue S A f (cosetRightMul S g q)) := by
  refine Quotient.ind' (fun x ↦ ?_) q
  change A.ρ x⁻¹ (f.1 (x * g)) = A.ρ g (A.ρ (x * g)⁻¹ (f.1 (x * g)))
  rw [← Module.End.mul_apply, ← map_mul]
  simp [mul_inv_rev, mul_assoc]

/-- The morphism (A\to \operatorname{Coind}_S^G \operatorname{Res}_S^G A)
induced by the identity of the restricted representation. -/
def unit : A ⟶ CoindRes S A :=
  Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _)

/-- Sum over the right cosets to trace the coinduced representation back to (A). -/
def trace [Finite G] : CoindRes S A ⟶ A := by
  classical
  letI := Fintype.ofFinite (RightCosets S)
  refine Rep.ofHom
    { toFun := fun f ↦ ∑ q : RightCosets S, normalizedValue S A f q
      map_add' := fun f h ↦ by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun q _ ↦ normalizedValue_add S A f h q)
      map_smul' := fun r f ↦ by
        change (∑ q : RightCosets S, normalizedValue S A (r • f) q) =
          r • ∑ q : RightCosets S, normalizedValue S A f q
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun q _ ↦ normalizedValue_smul S A r f q)
      isIntertwining' := fun g ↦ by
        ext f
        change (∑ q : RightCosets S, normalizedValue S A ((CoindRes S A).ρ g f) q) =
          A.ρ g (∑ q : RightCosets S, normalizedValue S A f q)
        calc
          _ = ∑ q : RightCosets S, A.ρ g (normalizedValue S A f (cosetRightMul S g q)) :=
            Finset.sum_congr rfl (fun q _ ↦ normalizedValue_action S A g f q)
          _ = A.ρ g (∑ q : RightCosets S, normalizedValue S A f (cosetRightMul S g q)) :=
            (map_sum (A.ρ g) _ _).symm
          _ = _ := congrArg (A.ρ g) ((cosetRightMul S g).sum_comp (normalizedValue S A f)) }

/-- The composite of the unit and trace is multiplication by the subgroup index. -/
theorem unit_trace [Finite G] : unit S A ≫ trace S A = S.index • (𝟙 A : A ⟶ A) := by
  classical
  letI := Fintype.ofFinite (RightCosets S)
  have hCard : Fintype.card (RightCosets S) = S.index := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)
  apply Rep.hom_ext
  ext a
  have hq (q : RightCosets S) : normalizedValue S A ((unit S A).hom a) q = a := by
    refine Quotient.ind' (fun x ↦ ?_) q
    change A.ρ x⁻¹ (((unit S A).hom a).1 x) = a
    rw [unit, Rep.resCoindToHom_hom_apply_coe, Rep.hom_id]
    change A.ρ x⁻¹ (A.ρ x a) = a
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  change (∑ q : RightCosets S, normalizedValue S A ((unit S A).hom a) q) =
    (S.index • (𝟙 A : A ⟶ A)).hom a
  simp only [hq, Finset.sum_const, Finset.card_univ, hCard, Rep.nsmul_hom, Rep.hom_id,
    Representation.IntertwiningMap.coe_nsmul, Pi.smul_apply, Representation.IntertwiningMap.id_apply]

end

end ManuscriptAudit.FiniteIndexCoinducedTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FiniteIndexCoinducedTrace.trace,
      ``ManuscriptAudit.FiniteIndexCoinducedTrace.unit_trace] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
