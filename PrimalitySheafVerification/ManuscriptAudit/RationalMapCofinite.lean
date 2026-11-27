import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.NormNum

/-! A rational function of strictly larger numerator degree has every target value
over an algebraically closed field away from the finitely many images of forbidden source points. -/

namespace ManuscriptAudit.RationalMapCofinite

open Polynomial

variable {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L]

/-- The normalized rational map has a preimage, avoiding a finite excluded source set. -/
theorem exists_preimage_away {N D : L[X]} (hDegree : D.natDegree < N.natDegree)
    (hCoprime : IsCoprime N D) (bad : Finset L) {r : L}
    (hr : r ∉ bad.image (fun x => N.eval x / D.eval x)) :
    ∃ x, x ∉ bad ∧ D.eval x ≠ 0 ∧ N.eval x / D.eval x = r := by
  let p := N - C r * D
  have hpos : 0 < N.natDegree := (Nat.zero_le _).trans_lt hDegree
  have hDeg : p.natDegree = N.natDegree := by
    apply natDegree_sub_eq_left_of_natDegree_lt
    by_cases h : r = 0
    · simpa only [h, C_0, zero_mul, natDegree_zero] using hpos
    · simpa only [natDegree_C_mul h] using hDegree
  have hp : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hDeg
    exact hpos.ne' hDeg.symm
  have hpDegree : p.degree ≠ 0 := by
    rw [degree_eq_natDegree hp]
    have hn : p.natDegree ≠ 0 := hDeg.symm ▸ hpos.ne'
    exact_mod_cast hn
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p hpDegree
  have hx' : N.eval x = r * D.eval x := by
    apply sub_eq_zero.mp
    simpa only [p, eval_sub, eval_mul, eval_C] using hx
  have hD : D.eval x ≠ 0 := by
    intro hd
    have hn : N.eval x = 0 := by rw [hx', hd, mul_zero]
    obtain ⟨a, b, he⟩ := hCoprime
    have hev := congrArg (fun f : L[X] => f.eval x) he
    simp only [eval_add, eval_mul, eval_one, hn, hd, mul_zero, add_zero] at hev
    exact (zero_ne_one : (0 : L) ≠ 1) hev
  have hValue := (div_eq_iff hD).mpr hx'
  exact ⟨x, fun hx => hr (Finset.mem_image.mpr ⟨x, hx, hValue⟩), hD, hValue⟩

end ManuscriptAudit.RationalMapCofinite

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RationalMapCofinite.exists_preimage_away
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
