import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Basis.Basic
import PrimalitySheafVerification.ManuscriptAudit.TwelveTorsionCRT

/-! The native rank-two basis of twelve-torsion obtained from the two residue bases. -/

namespace ManuscriptAudit.TwelveTorsionCRTBasis

open Module TorsionFrobeniusModule

noncomputable section

set_option maxHeartbeats 1100000

/-- The ring Chinese-remainder equivalence for the exact moduli four and three. -/
def coefficientCRT : ZMod 12 ≃+* ZMod 4 × ZMod 3 :=
  ZMod.chineseRemainder (m := 4) (n := 3) (by decide)

def reduceFour : ZMod 12 →+* ZMod 4 :=
  (RingHom.fst (ZMod 4) (ZMod 3)).comp coefficientCRT.toRingHom

def reduceThree : ZMod 12 →+* ZMod 3 :=
  (RingHom.snd (ZMod 4) (ZMod 3)).comp coefficientCRT.toRingHom

theorem reduce_injective {a b : ZMod 12} (h₄ : reduceFour a = reduceFour b)
    (h₃ : reduceThree a = reduceThree b) : a = b :=
  coefficientCRT.injective (Prod.ext h₄ h₃)

variable (G : Type*) [AddCommGroup G]
variable (B₄ : Basis (Fin 2) (ZMod 4) (Torsion 4 G))
variable (B₃ : Basis (Fin 2) (ZMod 3) (Torsion 3 G))

private def addCoordinates : Torsion 12 G ≃+ (Fin 2 → ZMod 12) := by
  let e := TwelveTorsionCRT.equivalence G
  refine
    { toFun := fun P j => coefficientCRT.symm
        (B₄.equivFun (e P).1 j, B₃.equivFun (e P).2 j)
      invFun := fun v => e.symm
        (B₄.equivFun.symm (fun j => (coefficientCRT (v j)).1),
          B₃.equivFun.symm (fun j => (coefficientCRT (v j)).2))
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro P
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · apply B₄.equivFun.injective
      funext j
      rw [B₄.equivFun.apply_symm_apply, coefficientCRT.apply_symm_apply]
    · apply B₃.equivFun.injective
      funext j
      rw [B₃.equivFun.apply_symm_apply, coefficientCRT.apply_symm_apply]
  · intro v
    funext j
    let coordinates : Torsion 4 G × Torsion 3 G :=
      (B₄.equivFun.symm (fun i => (coefficientCRT (v i)).1),
        B₃.equivFun.symm (fun i => (coefficientCRT (v i)).2))
    change coefficientCRT.symm
      (B₄.equivFun (e (e.symm coordinates)).1 j,
        B₃.equivFun (e (e.symm coordinates)).2 j) = v j
    rw [e.apply_symm_apply]
    unfold coordinates
    simp only [LinearEquiv.apply_symm_apply, Prod.eta, RingEquiv.symm_apply_apply]
  · intro P Q
    funext j
    change coefficientCRT.symm
      (B₄.equivFun (e (P + Q)).1 j, B₃.equivFun (e (P + Q)).2 j) =
      coefficientCRT.symm (B₄.equivFun (e P).1 j, B₃.equivFun (e P).2 j) +
        coefficientCRT.symm (B₄.equivFun (e Q).1 j, B₃.equivFun (e Q).2 j)
    rw [map_add e]
    simp only [Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply]
    exact coefficientCRT.symm.map_add
      (B₄.equivFun (e P).1 j, B₃.equivFun (e P).2 j)
      (B₄.equivFun (e Q).1 j, B₃.equivFun (e Q).2 j)

private def linearCoordinates : Torsion 12 G ≃ₗ[ZMod 12] (Fin 2 → ZMod 12) where
  toAddEquiv := addCoordinates G B₄ B₃
  map_smul' := by
    intro c P
    exact ZMod.map_smul (addCoordinates G B₄ B₃) c P

/-- Coordinatewise CRT joins the two checked native bases. -/
def basis : Basis (Fin 2) (ZMod 12) (Torsion 12 G) :=
  Basis.ofEquivFun (linearCoordinates G B₄ B₃)

theorem repr_reduce_four (P : Torsion 12 G) (i : Fin 2) :
    reduceFour ((basis G B₄ B₃).repr P i) = B₄.repr (TwelveTorsionCRT.equivalence G P).1 i := by
  unfold basis
  rw [Basis.ofEquivFun_repr_apply]
  change (coefficientCRT (coefficientCRT.symm
    (B₄.equivFun (TwelveTorsionCRT.equivalence G P).1 i,
      B₃.equivFun (TwelveTorsionCRT.equivalence G P).2 i))).1 = _
  rw [coefficientCRT.apply_symm_apply] <;> rfl

theorem repr_reduce_three (P : Torsion 12 G) (i : Fin 2) :
    reduceThree ((basis G B₄ B₃).repr P i) = B₃.repr (TwelveTorsionCRT.equivalence G P).2 i := by
  unfold basis
  rw [Basis.ofEquivFun_repr_apply]
  change (coefficientCRT (coefficientCRT.symm
    (B₄.equivFun (TwelveTorsionCRT.equivalence G P).1 i,
      B₃.equivFun (TwelveTorsionCRT.equivalence G P).2 i))).2 = _
  rw [coefficientCRT.apply_symm_apply] <;> rfl

theorem basis_components (i : Fin 2) :
    TwelveTorsionCRT.equivalence G (basis G B₄ B₃ i) = (B₄ i, B₃ i) := by
  apply Prod.ext
  · apply B₄.repr.injective
    apply Finsupp.ext
    intro j
    rw [← repr_reduce_four G B₄ B₃, Basis.repr_self_apply, Basis.repr_self_apply]
    split_ifs <;> simp
  · apply B₃.repr.injective
    apply Finsupp.ext
    intro j
    rw [← repr_reduce_three G B₄ B₃, Basis.repr_self_apply, Basis.repr_self_apply]
    split_ifs <;> simp

end
end ManuscriptAudit.TwelveTorsionCRTBasis

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwelveTorsionCRTBasis.basis_components
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
