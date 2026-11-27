import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.GCD.Basic

/-! An exact reindexing of the residues in one prescribed gcd class. -/

namespace ManuscriptAudit.Paper8GcdResidueFiber

def multiplyResidue {g n : ℕ} (hg : 0 < g) (i : Fin n) : Fin (g*n) :=
  ⟨g*i.val, mul_lt_mul_of_pos_left i.isLt hg⟩

theorem multiply_residue_gcd {g n : ℕ} (hg : 0 < g) (i : Fin n) (hi : Nat.Coprime i.val n) :
    Nat.gcd (multiplyResidue hg i).val (g*n) = g := by
  change Nat.gcd (g*i.val) (g*n) = g
  rw [Nat.gcd_mul_left, (show Nat.gcd i.val n = 1 from hi), mul_one]

noncomputable def fiber_bijection {g n : ℕ} (hg : 0 < g) :
    {i : Fin n // Nat.Coprime i.val n} ≃ {d : Fin (g*n) // Nat.gcd d.val (g*n) = g} := by
  let f (i : {i : Fin n // Nat.Coprime i.val n}) :
      {d : Fin (g*n) // Nat.gcd d.val (g*n) = g} :=
    ⟨multiplyResidue hg i.val, multiply_residue_gcd hg i.val i.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    have he' : g*i.val.val = g*j.val.val := congrArg (fun d => d.val.val) he
    exact Subtype.ext (Fin.ext (mul_left_cancel₀ hg.ne' he'))
  · intro d
    have hdvd : g ∣ d.val.val := by
      rw [← d.property]
      exact Nat.gcd_dvd_left _ _
    obtain ⟨u, hu⟩ := hdvd
    have hul : u < n := by
      by_contra! h
      have H : g*n ≤ g*u := Nat.mul_le_mul_left g h
      rw [← hu] at H
      exact (not_le_of_gt d.val.isLt) H
    have hc : Nat.Coprime u n := by
      have h := d.property
      rw [hu, Nat.gcd_mul_left] at h
      exact mul_left_cancel₀ hg.ne' (h.trans (mul_one g).symm)
    exact ⟨⟨⟨u,hul⟩,hc⟩, Subtype.ext (Fin.ext hu.symm)⟩

theorem sum_gcd_fiber {A : Type*} [AddCommMonoid A] {g n : ℕ} (hg : 0 < g)
    (w : Fin (g*n) → A) :
    (∑ d ∈ (Finset.univ.filter (fun d : Fin (g*n) => Nat.gcd d.val (g*n) = g)), w d) =
      ∑ i ∈ (Finset.univ.filter (fun i : Fin n => Nat.Coprime i.val n)), w (multiplyResidue hg i) := by
  classical
  symm
  refine Finset.sum_bij (fun i _ => multiplyResidue hg i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, multiply_residue_gcd hg i (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ he
    have h : g*i.val = g*j.val := congrArg Fin.val he
    exact Fin.ext (mul_left_cancel₀ hg.ne' h)
  · intro d hd
    let v : {d : Fin (g*n) // Nat.gcd d.val (g*n) = g} := ⟨d,(Finset.mem_filter.mp hd).2⟩
    let i := (fiber_bijection hg).symm v
    have h : fiber_bijection hg i = v := (fiber_bijection hg).apply_symm_apply v
    exact ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩,
      congrArg Subtype.val h⟩
  · intro i _
    rfl

end ManuscriptAudit.Paper8GcdResidueFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8GcdResidueFiber.multiply_residue_gcd,
      ``ManuscriptAudit.Paper8GcdResidueFiber.fiber_bijection,
      ``ManuscriptAudit.Paper8GcdResidueFiber.sum_gcd_fiber] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
