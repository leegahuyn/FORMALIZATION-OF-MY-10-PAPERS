import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RotationNormUnit
import PrimalitySheafVerification.ManuscriptAudit.PrimePrimaryCardinality

/-! The finite kernel of a scaled Eisenstein endomorphism gives an exact native torsion count. -/

namespace ManuscriptAudit.RotationKernelPrimaryCardinality

open TorsionFrobeniusModule RotationNormUnit PrimePrimaryCardinality

noncomputable section

variable {G : Type*} [AddCommGroup G]

private theorem apply_nsmul (n : ℕ) (f : AddMonoid.End G) (x : G) :
    (n • f) x = n • f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [succ_nsmul]
      change (n • f) x + f x = n • f x + f x
      rw [ih]

private def torsionKernelEquiv (m : ℕ) (U : AddMonoid.End G) :
    Torsion m ↥((m • U).ker) ≃ Torsion m G where
  toFun P := ⟨P.val.val, (mem_iff m G P.val.val).mpr
    (congrArg Subtype.val ((mem_iff m ↥((m • U).ker) P.val).mp P.property))⟩
  invFun P := by
    have hP := (mem_iff m G P.val).mp P.property
    have hK : P.val ∈ (m • U).ker := AddMonoidHom.mem_ker.mpr (by
      change (m • U : AddMonoid.End G) P.val = 0
      calc
        _ = m • U P.val := apply_nsmul m U P.val
        _ = U (m • P.val) := (map_nsmul U m P.val).symm
        _ = 0 := by rw [hP, map_zero])
    let Q : (m • U).ker := ⟨P.val, hK⟩
    exact ⟨Q, (mem_iff m ↥((m • U).ker) Q).mpr (Subtype.ext hP)⟩
  left_inv P := Subtype.ext (Subtype.ext rfl)
  right_inv P := Subtype.ext rfl

/-- An exact kernel order supplies the full prime-power torsion cardinal from the
integer norm of the residual rotation combination. -/
theorem card_torsion_of_kernel (l : ℕ) [Fact l.Prime] (n d : ℕ)
    (r : AddMonoid.End G) (hr : r ^ 2 + r + 1 = 0) (a b : ℤ)
    (hn : (d : ℤ) = a ^ 2 - a * b + b ^ 2) (hd : ¬l ∣ d)
    (hFinite : Finite ↥(((l ^ n : ℕ) • combination r a b).ker))
    (hK : Nat.card ↥(((l ^ n : ℕ) • combination r a b).ker) = (l ^ n) ^ 2 * d) :
    Nat.card (Torsion (l ^ n) G) = (l ^ 2) ^ n := by
  let U := combination r a b
  let V := combination r (a - b) (-b)
  let K := ↥(((l ^ n : ℕ) • U).ker)
  letI : Finite K := hFinite
  have hComb : V * U = (d : ℤ) • (1 : AddMonoid.End G) := by
    rw [hn, ← (combination_commute r a b (a - b) (-b)).eq]
    exact combination_mul_conjugate r hr a b
  have hAnn (P : K) : (l ^ n * d) • P = 0 := by
    apply Subtype.ext
    let x : G := P.val
    have hx : ((l ^ n : ℕ) • U) x = 0 := AddMonoidHom.mem_ker.mp P.property
    rw [apply_nsmul] at hx
    have hApply := congrArg V hx
    rw [map_nsmul, map_zero] at hApply
    have hV := congrArg (fun f : AddMonoid.End G => f x) hComb
    change (V * U) x = ((d : ℤ) • (1 : AddMonoid.End G)) x at hV
    rw [natCast_zsmul, apply_nsmul] at hV
    change V (U x) = d • x at hV
    change (l ^ n * d) • x = 0
    rw [mul_nsmul', ← hV]
    exact hApply
  exact (Nat.card_congr (torsionKernelEquiv (l ^ n) U)).symm.trans
    (card_torsion_of_annihilator K l n d d hd hd hAnn hK)

end
end ManuscriptAudit.RotationKernelPrimaryCardinality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RotationKernelPrimaryCardinality.card_torsion_of_kernel
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
