import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoReduction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicPowerSequence

/-! The actual adic Laurent class is a primitive integral line in the
proper cusp's native H². The quotient by that line has no prime-power
torsion. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoPrimitive

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CuspProperCompactification (projectiveCusp)
open CuspNativeAdicHTwoLower (adicInclusion)
open CuspNativeAdicHTwoReduction (residueInclusion residueInclusion_injective reduction_adicInclusion)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleAdicPowerSequence (multiply residue sequence sequence_shortExact)
open NativeAdicScalarAction (scalarMap scalarMap_zero scalarMap_one scalarMap_add)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveCusp K
private abbrev F := functions ℤ_[ℓ] (X K)
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology (X K)) AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift.{1} ℤ))

private theorem castScalar (m : ℕ) :
    scalarMap (X K) ℓ (m : ℤ_[ℓ]) = m • 𝟙 (F K ℓ) := by
  induction m with
  | zero => rw [Nat.cast_zero, scalarMap_zero, zero_nsmul]
  | succ m ih =>
    rw [Nat.cast_succ, scalarMap_add, scalarMap_one, ih, succ_nsmul]

private theorem nsmulId_HMap (n m : ℕ) (x : (X K).EllAdicCohomology ℓ n) :
    Sheaf.H.map (m • 𝟙 (F K ℓ)) n x = m • x := by
  induction m with
  | zero => simp [Sheaf.H.map_apply]
  | succ m ih =>
    change Sheaf.H.map ((m + 1) • 𝟙 (F K ℓ)) n x = (m + 1) • x
    simp only [add_nsmul, one_nsmul, Sheaf.H.map_add_apply, Sheaf.H.map_id_apply]
    exact congrArg (fun y : (X K).EllAdicCohomology ℓ n ↦ y + x) ih

private theorem power_HMap (n r : ℕ) (x : (X K).EllAdicCohomology ℓ n) :
    Sheaf.H.map (multiply (X K) ℓ r) n x = (ℓ ^ r : ℕ) • x := by
  change Sheaf.H.map (scalarMap (X K) ℓ ((ℓ : ℤ_[ℓ]) ^ r)) n x = _
  rw [← Nat.cast_pow, castScalar K ℓ]
  exact nsmulId_HMap K ℓ n (ℓ ^ r) x

/-- The actual integral proper H² has no prime-power torsion. -/
theorem power_nsmul_injective (r : ℕ) :
    Function.Injective (fun x : (X K).EllAdicCohomology ℓ 2 ↦ (ℓ ^ r : ℕ) • x) := by
  let S := sequence (X K) ℓ r
  let hs := sequence_shortExact (X K) ℓ r
  intro x y h
  apply sub_eq_zero.mp
  have hz : Sheaf.H.map S.f 2 (x - y) = 0 := by
    change Sheaf.H.map (multiply (X K) ℓ r) 2 (x - y) = 0
    rw [map_sub, power_HMap K ℓ 2 r x, power_HMap K ℓ 2 r y, h, sub_self]
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₁ (integers K) hs (x - y) hz
    (show 1 + 1 = 2 by rfl)
  have ha₀ : a = 0 :=
    (CuspNativeProetaleProperHOne.residue_HOne_subsingleton K ℓ r).elim _ _
  rw [ha₀, Ext.zero_comp] at ha
  exact ha.symm

private theorem reduction_nsmul_zero (r : ℕ) (x : (X K).EllAdicCohomology ℓ 2) :
    Sheaf.H.map (residue (X K) ℓ r) 2 ((ℓ ^ r : ℕ) • x) = 0 := by
  rw [← power_HMap K ℓ 2 r x, ← Sheaf.H.map_comp_apply]
  let S := sequence (X K) ℓ r
  change Sheaf.H.map (S.f ≫ S.g) 2 x = 0
  rw [S.zero]
  simp [Sheaf.H.map_apply]

/-- If a native proper H² class has a prime-power multiple in the actual
Laurent line, the class itself lies in that line. -/
theorem mem_range_of_power_nsmul_mem (r : ℕ) {x : (X K).EllAdicCohomology ℓ 2}
    (hx : (ℓ ^ r : ℕ) • x ∈ (adicInclusion K ℓ).range) :
    x ∈ (adicInclusion K ℓ).range := by
  obtain ⟨a, ha⟩ := hx
  have hr := reduction_adicInclusion K ℓ a r
  change Sheaf.H.map (residue (X K) ℓ r) 2 (adicInclusion K ℓ a) =
    residueInclusion K ℓ r (PadicInt.toZModPow r a) at hr
  rw [ha, reduction_nsmul_zero K ℓ r x, ← map_zero (residueInclusion K ℓ r)] at hr
  have h₀ : PadicInt.toZModPow r a = 0 := (residueInclusion_injective K ℓ r hr).symm
  have hker : a ∈ RingHom.ker (PadicInt.toZModPow r : ℤ_[ℓ] →+* ZMod (ℓ ^ r)) := h₀
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨b, hb⟩ := hker
  refine ⟨b, power_nsmul_injective K ℓ r ?_⟩
  rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, ← hb]
  exact ha

/-- No prime power kills any nonzero class in the quotient by the native adic line. -/
theorem quotient_power_torsionfree (r : ℕ)
    (x : (X K).EllAdicCohomology ℓ 2 ⧸ (adicInclusion K ℓ).range)
    (hx : (ℓ ^ r : ℕ) • x = 0) : x = 0 := by
  let N := (adicInclusion K ℓ).range
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk'_surjective N x
  subst x
  rw [← map_nsmul] at hx
  have h : (ℓ ^ r : ℕ) • y ∈ N := (QuotientAddGroup.eq_zero_iff _).mp hx
  exact (QuotientAddGroup.eq_zero_iff _).mpr (mem_range_of_power_nsmul_mem K ℓ r h)

end
end ManuscriptAudit.CuspNativeAdicHTwoPrimitive

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoPrimitive.power_nsmul_injective,
      ``ManuscriptAudit.CuspNativeAdicHTwoPrimitive.mem_range_of_power_nsmul_mem,
      ``ManuscriptAudit.CuspNativeAdicHTwoPrimitive.quotient_power_torsionfree] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
