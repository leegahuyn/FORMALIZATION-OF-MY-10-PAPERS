import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.GaloisField
import PrimalitySheafVerification.ManuscriptAudit.CubicThreePointCounts

/-! The rational vertical flexes are counted by their actual Frobenius sign. -/

namespace ManuscriptAudit.CubicThreeSquareRootDescent

open Polynomial CubicThreePointCounts CubicThreeTorsionOrdinate CubicThreeFrobeniusSigns

noncomputable section

variable {E L : Type*} [Field E] [Fintype E] [Field L] [Algebra E L]

/-- An element fixed by the cardinality power lies in the actual finite base field. -/
theorem fixed_scalar_iff (x : L) :
    x ^ Fintype.card E = x ↔ ∃ y : E, algebraMap E L y = x := by
  constructor
  · intro hx
    let f : E[X] := X ^ Fintype.card E - X
    have hf : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E Fintype.one_lt_card
    have hs : f.Splits := by
      rw [splits_iff_card_roots]
      change (X ^ Fintype.card E - X : E[X]).roots.card =
        (X ^ Fintype.card E - X : E[X]).natDegree
      rw [FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def, Finset.card_univ,
        FiniteField.X_pow_card_sub_X_natDegree_eq E Fintype.one_lt_card]
    have hRoot : (f.map (algebraMap E L)).IsRoot x := by
      simp [f, Polynomial.IsRoot, hx]
    exact hs.mem_range_of_isRoot hf hRoot
  · rintro ⟨y, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

private theorem ne_neg {K : Type*} [Field K] (h₂ : (2 : K) ≠ 0) {x : K} (hx : x ≠ 0) :
    x ≠ -x := by
  intro h
  apply mul_ne_zero h₂ hx
  calc
    (2 : K) * x = x + x := two_mul x
    _ = (-x) + x := congrArg (fun z => z + x) h
    _ = 0 := neg_add_cancel x

private theorem squareRoots_card_two (h₂ : (2 : E) ≠ 0) {A x : E}
    (hA : A ≠ 0) (hx : x ^ 2 = A) : Nat.card (SquareRoots A) = 2 := by
  classical
  have hx₀ : x ≠ 0 := by
    intro h
    exact hA (by simpa [h] using hx.symm)
  let f : Bool → SquareRoots A := fun s => ⟨signed s x, by cases s <;> simp [signed, hx]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      cases a <;> cases b
      · rfl
      · exact (ne_neg h₂ hx₀ (by simpa [f, signed] using (congrArg Subtype.val h).symm)).elim
      · exact (ne_neg h₂ hx₀ (by simpa [f, signed] using congrArg Subtype.val h)).elim
      · rfl
    · intro y
      rcases ordinate_eq_of_two_squares (y.property.trans hx.symm) with h | h
      · exact ⟨true, Subtype.ext (by simpa [f, signed] using h.symm)⟩
      · exact ⟨false, Subtype.ext (by simpa [f, signed] using h.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_bool]

/-- The number of rational square roots is two for the positive Frobenius sign and zero otherwise. -/
theorem squareRoots_card_of_sign (h₂ : (2 : E) ≠ 0) {A : E} (hA : A ≠ 0)
    {a : L} (ha : a ^ 2 = algebraMap E L A) {s : Bool}
    (hs : a ^ Fintype.card E = signed s a) :
    Nat.card (SquareRoots A) = if s then 2 else 0 := by
  classical
  have h₂L : (2 : L) ≠ 0 := by
    have hn : algebraMap E L (2 : E) ≠ 0 := (map_ne_zero (algebraMap E L)).mpr h₂
    simpa only [map_ofNat] using hn
  have ha₀ : a ≠ 0 := by
    intro h
    exact (map_ne_zero (algebraMap E L)).mpr hA (by simpa [h] using ha.symm)
  cases s with
  | false =>
    have hno : IsEmpty (SquareRoots A) := ⟨fun b => by
      have hb : (algebraMap E L b.val) ^ 2 = a ^ 2 := by
        rw [← map_pow, b.property, ha]
      obtain ⟨x, hx⟩ : ∃ x : E, algebraMap E L x = a := by
        rcases ordinate_eq_of_two_squares hb with he | he
        · exact ⟨b.val, he⟩
        · exact ⟨-b.val, by rw [map_neg, he, neg_neg]⟩
      have hfix := (fixed_scalar_iff (E := E) a).mpr ⟨x, hx⟩
      exact ne_neg h₂L ha₀ (hfix.symm.trans hs)⟩
    letI := hno
    letI : Fintype (SquareRoots A) := Fintype.ofFinite _
    simp [Nat.card_eq_fintype_card]
  | true =>
    obtain ⟨x, hx⟩ := (fixed_scalar_iff (E := E) a).mp hs
    have hxA : x ^ 2 = A :=
      (algebraMap E L).injective (by rw [map_pow, hx, ha])
    exact squareRoots_card_two h₂ hA hxA

end
end ManuscriptAudit.CubicThreeSquareRootDescent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeSquareRootDescent.fixed_scalar_iff,
      ``ManuscriptAudit.CubicThreeSquareRootDescent.squareRoots_card_of_sign] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
