import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFiniteFieldFixedCount

/-! Fixed torsion descent for arbitrary finite base and extension fields. -/

namespace ManuscriptAudit.WeierstrassGeneralFrobeniusTorsionFixed

open WeierstrassCurve TorsionFrobeniusModule CubicNonsplitFrobeniusTrace

noncomputable section

variable {K E L : Type*} [Field K] [Field E] [Fintype E] [DecidableEq E]
  [Field L] [DecidableEq L] [Algebra K E] [Algebra K L]

private theorem scalar_fixed_iff (i : E →ₐ[K] L) (x : L) :
    x ^ Fintype.card E = x ↔ ∃ y : E, i y = x := by
  letI : Algebra E L := i.toRingHom.toAlgebra
  exact WeierstrassFiniteFieldFixedCount.pow_card_eq_self_iff E L x

private theorem fixed_point_iff (i : E →ₐ[K] L) (g : L →ₐ[K] L)
    (hg : ∀ x, g x = x ^ Fintype.card E) (W : Affine K) (P : (W.baseChange L).Point) :
    Affine.Point.map (W' := W) g P = P ↔
      ∃ Q : (W.baseChange E).Point, Affine.Point.map (W' := W) i Q = P := by
  constructor
  · intro h
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x y hxy =>
      rw [Affine.Point.map_some] at h
      have hFixed := Affine.Point.some.inj h
      obtain ⟨a, ha⟩ := (scalar_fixed_iff i x).mp (by simpa only [hg] using hFixed.1)
      obtain ⟨b, hb⟩ := (scalar_fixed_iff i y).mp (by simpa only [hg] using hFixed.2)
      have h₀ : (W.baseChange E).Nonsingular a b :=
        (W.baseChange_nonsingular (f := i) i.injective a b).mp
          (by simpa only [ha, hb] using hxy)
      refine ⟨.some a b h₀, ?_⟩
      rw [Affine.Point.map_some]
      simpa only [Affine.Point.some.injEq] using And.intro ha hb
  · rintro ⟨Q, rfl⟩
    have hi : g.comp i = i := by
      ext a
      change g (i a) = i a
      rw [hg, ← map_pow, FiniteField.pow_card]
    rw [Affine.Point.map_map, hi]

private theorem fixed_torsion_iff (m : ℕ) (i : E →ₐ[K] L) (g : L →ₐ[K] L)
    (hg : ∀ x, g x = x ^ Fintype.card E) (W : Affine K)
    (P : Torsion m (W.baseChange L).Point) :
    pointMap m W g P = P ↔ ∃ Q : Torsion m (W.baseChange E).Point, pointMap m W i Q = P := by
  constructor
  · intro h
    have hp : Affine.Point.map (W' := W) g P.val = P.val := congrArg Subtype.val h
    obtain ⟨Q, hQ⟩ := (fixed_point_iff i g hg W P.val).mp hp
    have hT : m • Q = 0 := by
      apply Affine.Point.map_injective (W' := W) i
      rw [map_nsmul, map_zero, hQ]
      exact P.property
    exact ⟨⟨Q, hT⟩, Subtype.ext hQ⟩
  · rintro ⟨Q, hQ⟩
    apply Subtype.ext
    exact (fixed_point_iff i g hg W P.val).mpr ⟨Q.val, congrArg Subtype.val hQ⟩

/-- A scalar Frobenius of size `#E` fixes exactly the native rational torsion over `E`
in any chosen geometric model of the base-changed affine curve. -/
def rationalTorsionEquiv (m : ℕ) (i : E →ₐ[K] L) (g : L →ₐ[K] L)
    (hg : ∀ x, g x = x ^ Fintype.card E) (W : Affine K)
    (V : Affine L) (hW : W.baseChange L = V) :
    Torsion m (W.baseChange E).Point ≃
      {P : Torsion m V.Point // mapLinear m (pointMapAt K L W V hW g) P = P} := by
  subst V
  change Torsion m (W.baseChange E).Point ≃
    {P : Torsion m (W.baseChange L).Point // pointMap m W g P = P}
  exact Equiv.ofBijective (fun P => ⟨pointMap m W i P,
    (fixed_torsion_iff m i g hg W _).mpr ⟨P, rfl⟩⟩) (by
    constructor
    · intro a b h
      exact pointMap_injective m W i (congrArg Subtype.val h)
    · intro y
      obtain ⟨P, hP⟩ := (fixed_torsion_iff m i g hg W y.val).mp y.property
      exact ⟨P, Subtype.ext hP⟩)

end
end ManuscriptAudit.WeierstrassGeneralFrobeniusTorsionFixed

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassGeneralFrobeniusTorsionFixed.rationalTorsionEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
