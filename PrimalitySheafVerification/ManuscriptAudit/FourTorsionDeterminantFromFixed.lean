import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! The native fixed order-four points recover the supersingular determinant modulo four. -/

namespace ManuscriptAudit.FourTorsionDeterminantFromFixed

open FourTorsionDeterminantTools TorsionFrobeniusModule

noncomputable section

private theorem square_card_not_dvd_sixteen (q : ℕ) (hq : q % 4 = 1) :
    ¬16 ∣ (q + 1) ^ 2 := by
  intro h
  rw [Nat.dvd_iff_mod_eq_zero] at h
  have he : q + 1 = 4 * (q / 4) + 2 := by omega
  have hs : (q + 1) ^ 2 = 16 * ((q / 4) ^ 2 + q / 4) + 4 := by rw [he]; ring
  rw [hs, Nat.add_mod, Nat.mul_mod] at h
  norm_num at h

private theorem eight_dvd_square_card (q : ℕ) (hq : q % 4 = 3) : 8 ∣ (q + 1) ^ 2 := by
  have he : q + 1 = 4 * (q / 4 + 1) := by omega
  refine ⟨2 * (q / 4 + 1) ^ 2, ?_⟩
  rw [he]
  ring

variable {V H : Type*} [AddCommGroup V] [Module (ZMod 4) V]
  [AddCommGroup H] [Finite H]

/-- A genuine fixed-point descent identifies a trace-zero determinant via order-four torsion. -/
theorem determinant_eq_of_fixed_card (q : ℕ) (hq : Odd q)
    (B : Module.Basis (Fin 2) (ZMod 4) V) (F : V ≃ₗ[ZMod 4] V)
    (hTrace : LinearMap.trace (ZMod 4) V F.toLinearMap = 0)
    (hV : Nat.card V = 16) (hH : Nat.card H = (q + 1) ^ 2)
    (hKer : Nat.card (nsmulAddMonoidHom (2 : ℕ) : H →+ H).ker ≤ 4)
    (j : Torsion 4 H →+ V) (hj : Function.Injective j)
    (hFixed : ∀ v : V, F (F v) = v ↔ ∃ P : Torsion 4 H, j P = v) :
    LinearMap.det F.toLinearMap = (q : ZMod 4) := by
  obtain ⟨k, hk⟩ := hq
  have hqCases : q % 4 = 1 ∨ q % 4 = 3 := by omega
  have hSquare (v : V) : F (F v) = -(LinearMap.det F.toLinearMap) • v :=
    square_apply_of_trace_zero B F.toLinearMap hTrace v
  rcases determinant_cases F with hd | hd
  · have hq₁ : q % 4 = 1 := by
      rcases hqCases with h | h
      · exact h
      · have he : 8 ∣ Nat.card H := hH.symm ▸ eight_dvd_square_card q h
        obtain ⟨P, hP₄, hP₂⟩ := exists_orderFour he hKer
        let x : Torsion 4 H := ⟨P, (mem_iff 4 H _).mpr hP₄⟩
        have hFix : F (F (j x)) = j x := (hFixed _).mpr ⟨x, rfl⟩
        have hNeg : -(j x) = j x := by
          rw [hSquare, hd, neg_one_smul] at hFix
          exact hFix
        have hz : (2 : ℕ) • j x = 0 := by
          calc
            _ = j x + j x := two_nsmul _
            _ = -(j x) + j x := congrArg (fun y => y + j x) hNeg.symm
            _ = _ := neg_add_cancel _
        have hx₂ : (2 : ℕ) • x = 0 := hj (by rw [map_nsmul, map_zero, hz])
        exact (hP₂ (by
          have hc := congrArg (fun y : Torsion 4 H => (y : H)) hx₂
          change (2 : ℕ) • P = 0 at hc
          exact hc)).elim
    have hc : (q : ZMod 4) = 1 := by
      rw [← ZMod.natCast_mod q 4, hq₁, Nat.cast_one]
    exact hd.trans hc.symm
  · have hq₃ : q % 4 = 3 := by
      rcases hqCases with h | h
      · have hSurj : Function.Surjective j := by
          intro v
          apply (hFixed v).mp
          rw [hSquare, hd, show (-(3 : ZMod 4)) = 1 by decide, one_smul]
        have hT : Nat.card (Torsion 4 H) = 16 :=
          (Nat.card_congr (Equiv.ofBijective j ⟨hj, hSurj⟩)).trans hV
        have he := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (subgroup 4 H)
        change Nat.card H = Nat.card (H ⧸ subgroup 4 H) * Nat.card (Torsion 4 H) at he
        rw [hT] at he
        have hdvd : 16 ∣ Nat.card H := ⟨Nat.card (H ⧸ subgroup 4 H), he.trans (Nat.mul_comm _ _)⟩
        exact (square_card_not_dvd_sixteen q h (hH ▸ hdvd)).elim
      · exact h
    have hc : (q : ZMod 4) = 3 := by
      rw [← ZMod.natCast_mod q 4, hq₃, Nat.cast_ofNat]
    exact hd.trans hc.symm

end
end ManuscriptAudit.FourTorsionDeterminantFromFixed

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FourTorsionDeterminantFromFixed.determinant_eq_of_fixed_card
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
