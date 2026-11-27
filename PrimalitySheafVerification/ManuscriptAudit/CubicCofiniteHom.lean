import Lean.Util.CollectAxioms
import Mathlib.Data.Set.Finite.Lattice
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! Native point homomorphisms agree if they agree away from finitely many abscissas. -/

namespace ManuscriptAudit.CubicCofiniteHom

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate

noncomputable section

theorem addHom_ext {G H : Type*} [AddGroup G] [AddGroup H] [Infinite G]
    (f g : G →+ H) {S : Set G} (hS : S.Finite)
    (heq : ∀ P ∉ S, f P = g P) : f = g := by
  apply AddMonoidHom.ext
  intro P
  have hTrans : ((fun Q : G => P + Q) ⁻¹' S).Finite :=
    Set.Finite.preimage (fun _ _ _ _ h => add_left_cancel h) hS
  obtain ⟨Q, hQ⟩ := (hS.union hTrans).exists_notMem
  have heQ := heq Q (fun h => hQ (Or.inl h))
  have hePQ := heq (P + Q) (fun h => hQ (Or.inr h))
  exact add_right_cancel (show f P + g Q = g P + g Q by
    simpa only [map_add, heQ] using hePQ)

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {A : K}

theorem abscissa_surjective (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) :
    Function.Surjective (abscissa (A := A)) := by
  intro x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + A) zero_lt_two
  exact ⟨Affine.Point.some x y ((nonsingular_iff hΔ x y).mpr hy), rfl⟩

theorem finite_abscissa_fiber (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) (x : K) :
    ((abscissa (A := A)) ⁻¹' {x}).Finite := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + A) zero_lt_two
  have hn := (nonsingular_iff hΔ x y).mpr hy
  have hm := (nonsingular_iff hΔ x (-y)).mpr (by simpa only [neg_sq] using hy)
  have ht : ({0, Affine.Point.some x y hn, Affine.Point.some x (-y) hm} :
      Set (Curve A).Point).Finite := by simp
  refine ht.subset ?_
  intro P hP
  cases P with
  | zero => exact Or.inl rfl
  | some a b h =>
    have ha : a = x := hP
    subst a
    have hb := (nonsingular_iff hΔ x b).mp h
    rcases ordinate_eq_of_two_squares (hb.trans hy.symm) with hby | hby
    · subst b
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (show Affine.Point.some x b h = Affine.Point.some x (-y) hm by
        rw [Affine.Point.some.injEq]; exact ⟨rfl, hby⟩))

/-- On the actual group of a centered cubic, finitely many exceptional abscissas can be discarded. -/
theorem cubicHom_ext {H : Type*} [AddGroup H]
    (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) (f g : (Curve A).Point →+ H)
    {S : Set K} (hS : S.Finite)
    (heq : ∀ (x y : K) (h : (Curve A).Nonsingular x y), x ∉ S →
      f (Affine.Point.some x y h) = g (Affine.Point.some x y h)) : f = g := by
  letI : Infinite (Curve A).Point :=
    Infinite.of_surjective _ (abscissa_surjective hΔ)
  apply addHom_ext f g (hS.preimage' (fun x _ => finite_abscissa_fiber hΔ x))
  intro P hP
  cases P with
  | zero => exact (map_zero f).trans (map_zero g).symm
  | some x y h => exact heq x y h hP

end
end ManuscriptAudit.CubicCofiniteHom

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCofiniteHom.addHom_ext,
      ``ManuscriptAudit.CubicCofiniteHom.abscissa_surjective,
      ``ManuscriptAudit.CubicCofiniteHom.finite_abscissa_fiber,
      ``ManuscriptAudit.CubicCofiniteHom.cubicHom_ext] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
