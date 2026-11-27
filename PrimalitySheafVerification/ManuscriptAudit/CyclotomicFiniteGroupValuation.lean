import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! Inert prime valuations of a finite group with a cyclotomic automorphism. -/

namespace ManuscriptAudit.CyclotomicFiniteGroupValuation

private theorem two_pow_mod_three (n : ℕ) :
    (2 ^ n : ℕ) % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      by_cases h : n % 2 = 0
      · have hn : n.succ % 2 ≠ 0 := by omega
        simp [h, hn]
      · have hn : n.succ % 2 = 0 := by omega
        simp [h, hn]

private theorem cube_apply {G : Type*} [CommGroup G] (ρ : MulAut G)
    (hquad : ∀ x, ρ (ρ x) * ρ x * x = 1) (x : G) :
    ρ (ρ (ρ x)) = x := by
  apply mul_right_cancel (b := ρ (ρ x) * ρ x)
  calc
    ρ (ρ (ρ x)) * (ρ (ρ x) * ρ x) = 1 := by
      simpa only [mul_assoc] using hquad (ρ x)
    _ = x * (ρ (ρ x) * ρ x) := by
      rw [← hquad x]
      ac_rfl

/-- An inert prime occurs to even multiplicity in the order of a finite abelian group with
an automorphism annihilated by the third cyclotomic polynomial. -/
theorem multiplicative_factorization_even {G : Type*} [CommGroup G] [Finite G]
    (l : ℕ) [Fact l.Prime] (hl : l % 3 = 2) (ρ : MulAut G)
    (hquad : ∀ x, ρ (ρ x) * ρ x * x = 1) :
    Even ((Nat.card G).factorization l) := by
  let P : Sylow l G := default
  have hmap : P.toSubgroup.map ρ.toMonoidHom ≤ P.toSubgroup :=
    (P.isPGroup'.map ρ.toMonoidHom).le_sylow_of_normal P
  let φ : P.toSubgroup →* P.toSubgroup :=
    { toFun := fun x => ⟨ρ x.val, hmap ⟨x.val, x.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun x y => Subtype.ext (map_mul ρ x.val y.val) }
  have hφ : Function.Injective φ := by
    intro x y h
    exact Subtype.ext (ρ.injective (congrArg Subtype.val h))
  let e : MulAut P.toSubgroup := MulEquiv.ofBijective φ hφ.bijective_of_finite
  have he : e ^ 3 = 1 := by
    apply MulEquiv.ext
    intro x
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two]
    simp only [MulAut.mul_apply, MulAut.one_apply]
    apply Subtype.ext
    exact cube_apply ρ hquad x.val
  let C := Subgroup.zpowers e
  letI : MulAction C P.toSubgroup :=
    { smul := fun g x => g.val x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC : IsPGroup 3 C := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change g.val ^ (3 ^ 1) = 1
    rw [pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_mem_zpowers g.property).trans (orderOf_dvd_of_pow_eq_one he))
  have hfixed : MulAction.fixedPoints C P.toSubgroup = {1} := by
    ext x
    constructor
    · intro hx
      change ∀ g : C, g.val x = x at hx
      have hs : e x = x := hx ⟨e, Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one e⟩⟩
      have hρ : ρ x.val = x.val := congrArg Subtype.val hs
      have hx3 : x ^ 3 = 1 := by
        apply Subtype.ext
        change x.val ^ 3 = 1
        rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two]
        simpa only [hρ] using hquad x.val
      obtain ⟨n, hn⟩ := P.isPGroup' x
      have hc : Nat.Coprime 3 (l ^ n) :=
        (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega : ¬ 3 ∣ l)).pow_right n
      have hd : orderOf x ∣ 1 := by
        rw [← hc.gcd_eq_one]
        exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one hn)
      exact Set.mem_singleton_iff.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))
    · intro hx
      change x = 1 at hx
      subst x
      intro g
      exact map_one g.val
  have hcard : Nat.card P.toSubgroup ≡ 1 [MOD 3] := by
    simpa [hfixed] using hC.card_modEq_card_fixedPoints P.toSubgroup
  have hbase : l ≡ 2 [MOD 3] := hl
  rw [P.card_eq_multiplicity] at hcard
  have htwo := (hbase.pow ((Nat.card G).factorization l)).symm.trans hcard
  change (2 ^ (Nat.card G).factorization l : ℕ) % 3 = 1 at htwo
  rw [two_pow_mod_three] at htwo
  apply even_iff_two_dvd.mpr
  apply Nat.dvd_iff_mod_eq_zero.mpr
  by_contra hn
  simp [hn] at htwo

theorem additive_factorization_even {G : Type*} [AddCommGroup G] [Finite G]
    (l : ℕ) [Fact l.Prime] (hl : l % 3 = 2) (ρ : G ≃+ G)
    (hquad : ∀ x, ρ (ρ x) + ρ x + x = 0) :
    Even ((Nat.card G).factorization l) :=
  multiplicative_factorization_even (G := Multiplicative G) l hl
    (AddEquiv.toMultiplicative ρ) (fun x => hquad x.toAdd)

end ManuscriptAudit.CyclotomicFiniteGroupValuation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CyclotomicFiniteGroupValuation.multiplicative_factorization_even,
      ``ManuscriptAudit.CyclotomicFiniteGroupValuation.additive_factorization_even] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
