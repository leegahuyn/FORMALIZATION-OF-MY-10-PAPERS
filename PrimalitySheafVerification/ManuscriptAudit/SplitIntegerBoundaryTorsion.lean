import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! Prime-power torsion passes unchanged through a surjection whose
kernel is a primitive copy of the integers. -/

namespace ManuscriptAudit.SplitIntegerBoundaryTorsion

open PowerTateModule PowerTorsionTower TorsionFrobeniusModule

noncomputable section

variable {H P : Type*} [AddCommGroup H] [AddCommGroup P]
variable (b : ℤ →+ H) (r : H →+ P) (he : b.range = r.ker)

private theorem integer_nsmul_eq_zero (m : ℕ) (hm : m ≠ 0) {n : ℤ} (h : m • n = 0) : n = 0 := by
  rw [nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr hm)

include he in
/-- The integer boundary has no finite torsion, so the induced torsion
restriction is injective for every positive level. -/
theorem torsion_injective (hb : Function.Injective b) (m : ℕ) (hm : m ≠ 0) :
    Function.Injective (mapLinear m r) := by
  intro x y h
  have hxy : r (x : H) = r (y : H) := congrArg Subtype.val h
  have hk : (x : H) - (y : H) ∈ r.ker := by
    apply AddMonoidHom.mem_ker.mpr
    rw [map_sub, hxy, sub_self]
  rw [← he] at hk
  obtain ⟨n, hn⟩ := hk
  have hx : m • (x : H) = 0 := x.property
  have hy : m • (y : H) = 0 := y.property
  have ht : m • ((x : H) - (y : H)) = 0 := by rw [nsmul_sub, hx, hy, sub_self]
  have hM : m • n = 0 := hb (by rw [map_nsmul, hn, ht, map_zero])
  have hN : n = 0 := integer_nsmul_eq_zero m hm hM
  apply Subtype.ext
  exact sub_eq_zero.mp (hn.symm.trans (by rw [hN, map_zero]))

include he in
/-- A degree retraction corrects an arbitrary lift to a finite torsion
lift by subtracting its integral boundary component. -/
theorem torsion_surjective (hr : Function.Surjective r) (d : H →+ ℤ)
    (hd : Function.LeftInverse d b) (m : ℕ) : Function.Surjective (mapLinear m r) := by
  intro x
  obtain ⟨y, hy⟩ := hr (x : P)
  have hb (n : ℤ) : r (b n) = 0 := by
    apply AddMonoidHom.mem_ker.mp
    rw [← he]
    exact ⟨n, rfl⟩
  let z := y - b (d y)
  have hz : r z = (x : P) := by
    change r (y - b (d y)) = _
    rw [map_sub, hy, hb, sub_zero]
  have hzD : d z = 0 := by
    change d (y - b (d y)) = 0
    rw [map_sub, hd, sub_self]
  have ht : m • z ∈ r.ker := by
    apply AddMonoidHom.mem_ker.mpr
    rw [map_nsmul, hz]
    exact x.property
  rw [← he] at ht
  obtain ⟨n, hn⟩ := ht
  have hN := congrArg d hn
  rw [hd, map_nsmul, hzD, nsmul_zero] at hN
  have htz : m • z = 0 := hn.symm.trans (by rw [hN, map_zero])
  exact ⟨⟨z, htz⟩, Subtype.ext hz⟩

/-- A native Tate restriction is an isomorphism if it is bijective at each
of the actual compatible finite torsion levels. -/
theorem tate_bijective_of_levels (p : ℕ) [Fact p.Prime]
    (h : ∀ n : ℕ, Function.Bijective (mapLinear (p ^ n) r)) :
    Function.Bijective (PowerTateModule.map p r) := by
  constructor
  · intro x y hxy
    apply PowerTateModule.ext p H
    intro n
    apply (h n).1
    exact congrArg (evaluate p P n) hxy
  · intro x
    have hs (n : ℕ) := (h n).2 (evaluate p P n x)
    choose z hz using hs
    have comp (n : ℕ) : transition p H n (z (n + 1)) = z n := by
      apply (h n).1
      change mapAdd (p ^ n) r (transition p H n (z (n + 1))) = mapAdd (p ^ n) r (z n)
      have h₁ (k : ℕ) : mapAdd (p ^ k) r (z k) = evaluate p P k x := hz k
      rw [← map_transition, h₁, h₁, evaluate_transition]
    refine ⟨⟨z, comp⟩, PowerTateModule.ext p P ?_⟩
    intro n
    exact hz n

include he in
/-- A primitive integer boundary contributes no term to the genuine
compatible prime-power Tate module. -/
def tateEquiv (hr : Function.Surjective r) (d : H →+ ℤ) (hd : Function.LeftInverse d b)
    (p : ℕ) [Fact p.Prime] : Tate p H ≃ₗ[ℤ_[p]] Tate p P :=
  LinearEquiv.ofBijective (PowerTateModule.map p r)
    (tate_bijective_of_levels r p fun n =>
      ⟨torsion_injective b r he hd.injective _ (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero),
        torsion_surjective b r he hr d hd _⟩)

end

end ManuscriptAudit.SplitIntegerBoundaryTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SplitIntegerBoundaryTorsion.torsion_injective,
      ``ManuscriptAudit.SplitIntegerBoundaryTorsion.torsion_surjective,
      ``ManuscriptAudit.SplitIntegerBoundaryTorsion.tateEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
