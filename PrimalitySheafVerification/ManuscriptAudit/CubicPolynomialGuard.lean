import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots

/-! A list of nonzero polynomial guards excludes only finitely many abscissas. -/

namespace ManuscriptAudit.CubicPolynomialGuard

open Polynomial

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

def Exceptional (P : List k[X]) : Set L :=
  {x | ∃ f ∈ P, f.eval₂ (algebraMap k L) (x ^ 3) = 0}

theorem evaluate_ne_zero {P : List k[X]} {x : L} (hx : x ∉ Exceptional (L := L) P)
    {f : k[X]} (hf : f ∈ P) : f.eval₂ (algebraMap k L) (x ^ 3) ≠ 0 :=
  fun h => hx ⟨f, hf, h⟩

private theorem one_guard_finite (f : k[X]) (hf : f ≠ 0) :
    ({x : L | f.eval₂ (algebraMap k L) (x ^ 3) = 0} : Set L).Finite := by
  let q := f.map (algebraMap k L)
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap k L).injective).mpr hf
  have hdeg : (X ^ 3 : L[X]).natDegree ≠ 0 := by simp
  have hne : q.comp (X ^ 3) ≠ 0 := by
    intro hz
    have hlc := leadingCoeff_comp (p := q) (q := X ^ 3) hdeg
    rw [hz, leadingCoeff_zero] at hlc
    have hlt : ((X ^ 3 : L[X]).leadingCoeff) ^ q.natDegree ≠ 0 := by simp
    exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hq) hlt) hlc.symm
  refine (finite_setOf_isRoot hne).subset ?_
  intro x hx
  change f.eval₂ (algebraMap k L) (x ^ 3) = 0 at hx
  change (q.comp (X ^ 3)).eval x = 0
  rw [eval_comp, eval_pow, eval_X]
  simpa only [q, eval_map] using hx

theorem exceptional_finite (P : List k[X]) (hP : ∀ f ∈ P, f ≠ 0) :
    (Exceptional (L := L) P).Finite := by
  induction P with
  | nil => simp [Exceptional]
  | cons f P ih =>
    have h₁ := one_guard_finite (L := L) f (hP f (by simp))
    have h₂ := ih (fun p hp => hP p (List.mem_cons_of_mem f hp))
    refine (h₁.union h₂).subset ?_
    rintro x ⟨p, hp, hpx⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl hpx
    · exact Or.inr ⟨p, hp, hpx⟩

end ManuscriptAudit.CubicPolynomialGuard

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicPolynomialGuard.exceptional_finite
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
