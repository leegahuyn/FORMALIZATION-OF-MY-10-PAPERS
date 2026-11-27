import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationModFourModel
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCentralizer

/-! Transport of the exact mod-four fixed-count model to an actual cyclic rotation basis. -/

namespace ManuscriptAudit.CubicRotationModFourKernel

open Module CubicRotationModFourModel CubicRotationCentralizer

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 4) V]

def coordinates (B : Basis (Fin 2) (ZMod 4) V) : V ≃ₗ[ZMod 4] Coordinates :=
  B.equivFun.trans (LinearEquiv.finTwoArrow (ZMod 4) (ZMod 4))

private theorem coordinates_apply (B : Basis (Fin 2) (ZMod 4) V) (x : V) :
    coordinates B x = (B.repr x 0, B.repr x 1) := rfl

theorem coordinates_action (B : Basis (Fin 2) (ZMod 4) V)
    (S : Module.End (ZMod 4) V) (h₀ : S (B 0) = B 1) (h₁ : S (B 1) = -B 0 - B 1)
    (a b : ZMod 4) (x : V) :
    coordinates B ((a • (1 : Module.End (ZMod 4) V) + b • S) x) =
      action a b (coordinates B x) := by
  let p := B.repr x 0
  let q := B.repr x 1
  have hx : p • B 0 + q • B 1 = x := by
    simpa only [p, q, Fin.sum_univ_two] using B.sum_repr x
  have hSx : S x = p • B 1 + q • (-B 0 - B 1) := by
    calc
      S x = S (p • B 0 + q • B 1) := congrArg S hx.symm
      _ = _ := by rw [map_add, map_smul, map_smul, h₀, h₁]
  change coordinates B (a • x + b • S x) = _
  rw [hSx]
  apply Prod.ext <;> simp [coordinates_apply, action, Basis.repr_self, p, q, smul_eq_mul] <;> ring

theorem fixed_card (e : V ≃ Coordinates) (F : V → V)
    (M : Coordinates → Coordinates) (h : ∀ x, e (F x) = M (e x)) :
    Nat.card {x : V // F x = x} = fixedCount M := by
  let ee : {x : V // F x = x} ≃ {x : Coordinates // M x = x} :=
    { toFun := fun x => ⟨e x.val, (h x.val).symm.trans (congrArg e x.property)⟩
      invFun := fun x => ⟨e.symm x.val, e.injective (by
        rw [h, e.apply_symm_apply, x.property])⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val) }
  rw [Nat.card_congr ee]
  simp only [fixedCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Exact alternatives for the points fixed by the cubic iterate and its negative. -/
def CubeFixedPatterns (F : Module.End (ZMod 4) V) : Prop :=
  (∀ x : V, (2 : ℕ) • x = 0 → (F ^ 3) x = x ∧ -(F ^ 3) x = x) ∧
    ((LinearMap.det F = 1 ∧
      ((Nat.card {x : V // (F ^ 3) x = x} = 16 ∧
        Nat.card {x : V // -(F ^ 3) x = x} = 4) ∨
       (Nat.card {x : V // (F ^ 3) x = x} = 4 ∧
        Nat.card {x : V // -(F ^ 3) x = x} = 16))) ∨
     (LinearMap.det F = 3 ∧ Nat.card {x : V // (F ^ 3) x = x} = 4 ∧
       Nat.card {x : V // -(F ^ 3) x = x} = 4))

/-- The sign-fixed subgroups of an actual rotation-algebra operator have the tabulated sizes. -/
theorem cube_fixed_patterns (B : Basis (Fin 2) (ZMod 4) V)
    (S F : Module.End (ZMod 4) V) (h₀ : S (B 0) = B 1) (h₁ : S (B 1) = -B 0 - B 1)
    (a b : ZMod 4) (hF : F = a • 1 + b • S)
    (hd : LinearMap.det F = 1 ∨ LinearMap.det F = 3) :
    CubeFixedPatterns F := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  let M := fun v => action a b (action a b (action a b v))
  have hNorm : LinearMap.det F = norm a b := by
    rw [hF]
    exact (trace_det_of_form B S h₀ h₁ a b).2
  have hu : norm a b = 1 ∨ norm a b = 3 := hNorm ▸ hd
  have h := CubicRotationModFourModel.cube_fixed_patterns a b hu
  have ha (x : V) : coordinates B (F x) = action a b (coordinates B x) := by
    rw [hF]
    exact coordinates_action B S h₀ h₁ a b x
  have hc (x : V) : coordinates B ((F ^ 3) x) = M (coordinates B x) := by
    change coordinates B (F (F (F x))) = _
    simp only [ha, M]
  have hn (x : V) : coordinates B (-(F ^ 3) x) = -M (coordinates B x) := by
    rw [map_neg, hc]
  unfold CubeFixedPatterns
  constructor
  · intro x hx
    have hz : (2 : ℕ) • coordinates B x = 0 := by
      rw [← map_nsmul, hx, map_zero]
    obtain ⟨hp, hm⟩ := h.1 (coordinates B x) hz
    exact ⟨(coordinates B).injective ((hc x).trans hp), (coordinates B).injective ((hn x).trans hm)⟩
  · rw [hNorm, fixed_card (coordinates B).toEquiv _ M hc,
      fixed_card (coordinates B).toEquiv _ (fun v => -M v) hn]
    exact h.2

end
end ManuscriptAudit.CubicRotationModFourKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotationModFourKernel.cube_fixed_patterns
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
