import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.LaurentKummerTowerAlgebra

/-! Actual finite Laurent stages form an increasing union in the
algebra carrying all Laurent-coordinate roots. -/

namespace ManuscriptAudit.LaurentKummerTowerFiniteStages

open LaurentKummerTowerAlgebra (Exponent Tower rootExponent rootExponent_succ exponent_from_finite_stage)

noncomputable section

variable (K : Type*) [CommRing K] (ℓ : ℕ)

/-- The exponent map of the actual stage. -/
def stageExponent (n : ℕ) : ℤ →+ Exponent ℓ where
  toFun z := z • rootExponent ℓ n
  map_zero' := zero_zsmul _
  map_add' a b := add_zsmul _ a b

/-- The finite Laurent stage embeds its coordinate as the chosen power root. -/
def stageMap (n : ℕ) : LaurentPolynomial K →+* Tower K ℓ :=
  AddMonoidAlgebra.mapDomainRingHom K (stageExponent ℓ n)

private def linkExponent : ℤ →+ ℤ where
  toFun z := ℓ • z
  map_zero' := smul_zero ℓ
  map_add' a b := smul_add ℓ a b

/-- From one finite Laurent stage to the next, use the power of its coordinate. -/
def link : LaurentPolynomial K →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapDomainRingHom K (linkExponent ℓ)

private theorem stageExponent_comp (n : ℕ) :
    (stageExponent ℓ (n + 1)).comp (linkExponent ℓ) = stageExponent ℓ n := by
  apply AddMonoidHom.ext
  intro z
  change (ℓ • z) • rootExponent ℓ (n + 1) = z • rootExponent ℓ n
  simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have h : (ℓ : Exponent ℓ) * rootExponent ℓ (n + 1) = rootExponent ℓ n := by
    simpa only [nsmul_eq_mul] using rootExponent_succ ℓ n
  calc
    _ = (z : Exponent ℓ) * ((ℓ : Exponent ℓ) * rootExponent ℓ (n + 1)) := by ring
    _ = _ := by rw [h]

theorem stageMap_comp_link (n : ℕ) :
    (stageMap K ℓ (n + 1)).comp (link K ℓ) = stageMap K ℓ n := by
  change (AddMonoidAlgebra.mapDomainRingHom K (stageExponent ℓ (n + 1))).comp
      (AddMonoidAlgebra.mapDomainRingHom K (linkExponent ℓ)) =
    AddMonoidAlgebra.mapDomainRingHom K (stageExponent ℓ n)
  rw [← AddMonoidAlgebra.mapDomainRingHom_comp, stageExponent_comp]

abbrev stage (n : ℕ) : Subring (Tower K ℓ) := (stageMap K ℓ n).range

theorem stage_mono : Monotone (stage K ℓ) :=
  monotone_nat_of_le_succ (fun n x hx ↦ by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨link K ℓ y, ?_⟩
    exact RingHom.congr_fun (stageMap_comp_link K ℓ n) y)

private theorem stage_single (n : ℕ) (z : ℤ) (a : K) :
    stageMap K ℓ n (AddMonoidAlgebra.single z a) = AddMonoidAlgebra.single (stageExponent ℓ n z) a :=
  AddMonoidAlgebra.mapDomain_single

/-- Every element, including arbitrary finite linear combinations of monomials,
is in the image of a single actual finite Laurent stage. -/
theorem exists_stage (v : Tower K ℓ) : ∃ n : ℕ, ∃ u : LaurentPolynomial K, stageMap K ℓ n u = v := by
  let S := ⨆ n, stage K ℓ n
  have hScalar (a : K) : algebraMap K (Tower K ℓ) a ∈ S := by
    apply (le_iSup (stage K ℓ) 0)
    refine ⟨AddMonoidAlgebra.single 0 a, ?_⟩
    rw [stage_single, map_zero]
    rfl
  have hV : v ∈ S := by
    apply AddMonoidAlgebra.induction_on v
    · intro x
      obtain ⟨n, z, hz⟩ := exponent_from_finite_stage ℓ x
      apply (le_iSup (stage K ℓ) n)
      refine ⟨AddMonoidAlgebra.single z 1, ?_⟩
      rw [stage_single, AddMonoidAlgebra.of_apply]
      change AddMonoidAlgebra.single (z • rootExponent ℓ n) (1 : K) = AddMonoidAlgebra.single x 1
      rw [hz]
    · intro a b ha hb
      exact S.add_mem ha hb
    · intro a v hv
      have h : a • v = algebraMap K (Tower K ℓ) a * v := Algebra.smul_def a v
      exact Eq.mpr (congrArg (fun b : Tower K ℓ ↦ b ∈ S) h) (S.mul_mem (hScalar a) hv)
  have hdir : Directed (· ≤ ·) (stage K ℓ) := (stage_mono K ℓ).directed_le
  exact (Subring.mem_iSup_of_directed hdir).mp hV

private theorem base_pow_mul_rootExponent (n : ℕ) :
    (ℓ : Exponent ℓ) ^ n * rootExponent ℓ n = 1 := by
  have h : (ℓ : Exponent ℓ) * (IsLocalization.Away.invSelf (ℓ : ℤ) : Exponent ℓ) = 1 := by
    simpa only [map_natCast] using
      (IsLocalization.Away.mul_invSelf (S := Exponent ℓ) (ℓ : ℤ))
  rw [rootExponent, ← mul_pow, h, one_pow]

/-- A finite stage lies over the original Laurent algebra by its exact `ℓ^n`-power map. -/
theorem stageMap_comp_base (n : ℕ) :
    (stageMap K ℓ n).comp (link K (ℓ ^ n)) = LaurentKummerTowerAlgebra.laurentMap K ℓ := by
  have h : (stageExponent ℓ n).comp (linkExponent (ℓ ^ n)) =
      (algebraMap ℤ (Exponent ℓ)).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro z
    change (ℓ ^ n • z) • rootExponent ℓ n = algebraMap ℤ (Exponent ℓ) z
    rw [nsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
    rw [mul_comm ((ℓ : Exponent ℓ) ^ n), mul_assoc, base_pow_mul_rootExponent, mul_one]
    exact (map_intCast (algebraMap ℤ (Exponent ℓ)) z).symm
  change (AddMonoidAlgebra.mapDomainRingHom K (stageExponent ℓ n)).comp
      (AddMonoidAlgebra.mapDomainRingHom K (linkExponent (ℓ ^ n))) = _
  rw [← AddMonoidAlgebra.mapDomainRingHom_comp, h]
  rfl

private theorem exponent_algebraMap_injective (hℓ : ℓ ≠ 0) :
    Function.Injective (algebraMap ℤ (Exponent ℓ)) := by
  apply IsLocalization.injective (M := Submonoid.powers (ℓ : ℤ)) (Exponent ℓ)
  rintro _ ⟨n, rfl⟩
  have hn : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hn)

theorem stageMap_injective (hℓ : ℓ ≠ 0) (n : ℕ) : Function.Injective (stageMap K ℓ n) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro z z' h
  change z • rootExponent ℓ n = z' • rootExponent ℓ n at h
  simp only [zsmul_eq_mul] at h
  have he := congrArg (fun x : Exponent ℓ ↦ x * (ℓ : Exponent ℓ) ^ n) h
  have hi : rootExponent ℓ n * (ℓ : Exponent ℓ) ^ n = 1 :=
    (mul_comm _ _).trans (base_pow_mul_rootExponent ℓ n)
  simp only [mul_assoc, hi, mul_one] at he
  apply exponent_algebraMap_injective ℓ hℓ
  calc
    _ = (z : Exponent ℓ) := map_intCast (algebraMap ℤ (Exponent ℓ)) z
    _ = (z' : Exponent ℓ) := he
    _ = _ := (map_intCast (algebraMap ℤ (Exponent ℓ)) z').symm

theorem laurentMap_injective (hℓ : ℓ ≠ 0) :
    Function.Injective (LaurentKummerTowerAlgebra.laurentMap K ℓ) :=
  AddMonoidAlgebra.mapDomain_injective (exponent_algebraMap_injective ℓ hℓ)

end
end ManuscriptAudit.LaurentKummerTowerFiniteStages

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.LaurentKummerTowerFiniteStages.stageMap_comp_link,
      ``ManuscriptAudit.LaurentKummerTowerFiniteStages.stage_mono,
      ``ManuscriptAudit.LaurentKummerTowerFiniteStages.exists_stage,
      ``ManuscriptAudit.LaurentKummerTowerFiniteStages.stageMap_comp_base,
      ``ManuscriptAudit.LaurentKummerTowerFiniteStages.stageMap_injective,
      ``ManuscriptAudit.LaurentKummerTowerFiniteStages.laurentMap_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
